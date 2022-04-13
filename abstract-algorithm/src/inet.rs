use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use ghost_cell::{GhostCell, GhostToken};

use crate::lambda::Term;

macro_rules! debug_println {
    ($($arg:tt)*) => (#[cfg(debug_print)] println!($($arg)*));
}

/// | Agent | Port 1 (principal) | Port 2 | Port 3 |
/// |-------|--------------------|--------|--------|
/// | Γ(Λ)  | result             | arg    | body   |
/// | Γ(Α)  | func               | arg    | result |
/// | Δ     | arg                | left   | right  |
/// | Ε     | target             | n/a    | n/a    |
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum AgentType {
    /// The root of the evaluation tree. There should only ever be one of these agents. The root
    /// should not interact with any other nodes; that is, it should have no principal port, and
    /// port 1 is used instead.
    Root,
    /// The γ agent, which functions both as λ and α when translating lambda calculus.
    Γ(ΓTag),
    /// The δ agent, which is used to duplicate lambda arguments that are used more than once.
    /// Since each δ corresponds to a unique lambda argument, two interacting δs for different
    /// arguments should commute, not annihilate, and so δ during translation receives a unique
    /// tag.
    Δ(usize),
    /// The ε agent, which is used to eliminate lambda arguments that are not used in the body.
    Ε,
}

/// λ and α are both implemented as Γ, but must be differentiated for the reverse lambda
/// translation.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ΓTag {
    /// abstraction
    Λ,
    /// application
    Α,
}

// TODO: model this without unsafe indexing
type Port<'id> = (AgentRef<'id>, usize);
type PortRef<'id, 'a> = (&'a AgentRef<'id>, usize);
const MAX_PORTS: usize = 3;
type AgentRef<'id> = Arc<GhostCell<'id, Agent<'id>>>;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
struct AgentId(usize);

impl AgentId {
    fn new() -> Self {
        static AGENT_ID_COUNTER: AtomicUsize = AtomicUsize::new(1);
        AgentId(AGENT_ID_COUNTER.fetch_add(1, Ordering::Relaxed))
    }
}

struct Agent<'id> {
    agent_type: AgentType,
    ports: [Option<Port<'id>>; MAX_PORTS],
    id: AgentId,
}

impl<'id> Agent<'id> {
    fn new(agent_type: AgentType) -> Self {
        Agent {
            agent_type,
            id: AgentId::new(),
            ports: Default::default(),
        }
    }

    fn new_ref(agent_type: AgentType) -> AgentRef<'id> {
        Arc::new(GhostCell::new(Agent::new(agent_type)))
    }

    fn target<'a>(&'a self, port_num: usize) -> Option<(&'a AgentRef<'id>, usize)> {
        self.ports[port_num].as_ref().map(|t| (&t.0, t.1))
    }

    /// Like [unlink], but unidirectional. Returns the old port. Assumes that the old
    /// target of the node will be unlinked; if not, behavior is undefined.
    fn unsafe_take<'a>(
        token: &'a mut GhostToken<'id>,
        port: PortRef<'id, 'a>,
    ) -> Option<Port<'id>> {
        debug_println!(
            "unlinking: ({:?}, {:?})",
            port.0.borrow(token).agent_type,
            port.1
        );
        port.0.borrow_mut(token).ports[port.1].take()
    }

    /// Unlink the port of the given agent and its target
    fn unlink<'a>(
        token: &'a mut GhostToken<'id>,
        port: PortRef<'id, 'a>,
    ) -> (Option<Port<'id>>, Option<Port<'id>>) {
        if let Some((target, target_port_num)) = Agent::unsafe_take(token, port) {
            let res = Agent::unsafe_take(token, (&target, target_port_num));
            (Some((target, target_port_num)), res)
        } else {
            (None, None)
        }
    }

    /// Link the two agents at the specified ports, but do not unlink the ports first. If the ports
    /// hvae old targets and they are not relinked afterwards, behavior is undefined.
    fn unsafe_link<'a>(token: &'a mut GhostToken<'id>, p1: PortRef<'id, 'a>, p2: PortRef<'id, 'a>) {
        debug_println!(
            "linking: ({:?}, {:?}) to ({:?}, {:?})",
            p1.0.borrow(token).agent_type,
            p1.1,
            p2.0.borrow(token).agent_type,
            p2.1
        );
        p1.0.borrow_mut(token).ports[p1.1] = Some((Arc::clone(p2.0), p2.1));
        p2.0.borrow_mut(token).ports[p2.1] = Some((Arc::clone(p1.0), p1.1));
    }

    /// Unlink all ports of an agent and destroy it
    fn destroy<'a>(token: &'a mut GhostToken<'id>, a: &'a AgentRef<'id>) {
        for i in 0..MAX_PORTS {
            Agent::unlink(token, (a, i));
        }
    }

    /// Link `p1` to the target of `p2`, unlinking `p2` in the process. You must verify that the
    /// old target of `p1` is unlinked.
    fn unsafe_link_to_target_of<'a>(
        token: &'a mut GhostToken<'id>,
        p1: PortRef<'id, 'a>,
        p2: PortRef<'id, 'a>,
    ) {
        // SAFETY: `p2_target` is relinked in the next line.
        if let Some(p2_target) = Agent::unsafe_take(token, p2) {
            Agent::unsafe_link(token, p1, (&p2_target.0, p2_target.1));
        } else {
            Agent::unsafe_take(token, p1);
        }
    }

    /// Apply the annihilation rule to two nodes of the same type that both have arity 2 (in
    /// particular, γ and δ) interacting at their principal ports. Does not check these
    /// preconditions! This should be used as a helper in interactions only.
    fn annihilate2<'a>(token: &'a mut GhostToken<'id>, a: &'a AgentRef<'id>, b: &'a AgentRef<'id>) {
        fn relink<'id, 'a>(
            token: &'a mut GhostToken<'id>,
            p1: PortRef<'id, 'a>,
            p2: PortRef<'id, 'a>,
        ) {
            // SAFETY: p1 and p2 point to the two ports which will be relinked together
            let a_dest: Option<Port<'id>> = Agent::unsafe_take(token, p1);
            let b_dest: Option<Port<'id>> = Agent::unsafe_take(token, p2);
            if let Some(a_dest1) = a_dest {
                if let Some(b_dest1) = b_dest {
                    // SAFETY: a_dest and b_dest used to be linked to p1 and p2, which we already
                    // unlinked above.
                    Agent::unsafe_link(token, (&a_dest1.0, a_dest1.1), (&b_dest1.0, b_dest1.1));
                } else {
                    Agent::unlink(token, (&a_dest1.0, a_dest1.1));
                }
            } else if let Some(b_dest1) = b_dest {
                Agent::unlink(token, (&b_dest1.0, b_dest1.1));
            }
        }
        Agent::unlink(token, (a, 0)); // unlink BOTH principal ports (for GC reasons)
        relink(token, (a, 1), (b, 1));
        relink(token, (a, 2), (b, 2));
        // all ports on a, b should be unlinked
    }

    /// Apply the commuting rule to two nodes of different types that both have arity 2 (in
    /// particular, γ and δ) interacting at their principal ports. Does not check these
    /// preconditions! This should be used as a helper in interactions only.
    fn commute2<'a>(token: &'a mut GhostToken<'id>, a: &'a AgentRef<'id>, b: &'a AgentRef<'id>) {
        let a2: AgentRef = Agent::new_ref(a.borrow(token).agent_type);
        let b2: AgentRef = Agent::new_ref(b.borrow(token).agent_type);
        // SAFETY: (b, 0) used to be linked to (a, 0), which is relinked in line 2.
        // SAFETY: target of (a, 1) used to be linked to (a, 1), which is unlinked here and relinked in line 3.
        Agent::unsafe_link_to_target_of(token, (b, 0), (a, 1));
        // SAFETY: (a, 0) used to be linked to (b, 0), which was relinked in line 1.
        // SAFETY: target of (b, 1) used to be linked to (b, 1), which is unlinked here and relinked in line 3.
        Agent::unsafe_link_to_target_of(token, (a, 0), (b, 1));
        // SAFETY: (b, 1) was unlinked in line 2.
        // SAFETY: (a, 1) was unlinked in line 1
        Agent::unsafe_link(token, (b, 1), (a, 1));
        // SAFETY: (b2, 0) is unlinked by default.
        // SAFETY: target of (a, 2) used to be linked to (a, 2), which is unlinked here and relinked in line 6.
        Agent::unsafe_link_to_target_of(token, (&b2, 0), (a, 2));
        // SAFETY: (a2, 0) is unlinked by default.
        // SAFETY: target of (b, 2) used to be linked to (b, 2), which is unlinked here and relinked in line 6.
        Agent::unsafe_link_to_target_of(token, (&a2, 0), (b, 2));
        // SAFETY: (a, 2) is unlinked in line 4.
        // SAFETY: (b2, 1) is unlinked by default.
        Agent::unsafe_link(token, (a, 2), (&b2, 1));
        // SAFETY: (b, 2) is unlinked in line 5.
        // SAFETY: (a2, 1) is unlinked by default.
        Agent::unsafe_link(token, (b, 2), (&a2, 1));
        // SAFETY: (b2, 2) is unlinked by default.
        // SAFETY: (a2, 2) is unlinked by default.
        Agent::unsafe_link(token, (&b2, 2), (&a2, 2));
    }

    /// Applies the erasing rule on an arity-2 agent interacting with an ε agent at its principal
    /// port. Assumes that that exactly one of the nodes is an ε agent, and that they are already
    /// connected.
    fn erase2<'a>(token: &'a mut GhostToken<'id>, a: &'a AgentRef<'id>, b: &'a AgentRef<'id>) {
        let (erase, target) = if a.borrow(token).agent_type == AgentType::Ε {
            (a, b)
        } else {
            (b, a)
        };
        Agent::unlink(token, (erase, 0)); // should also unlink target's principal port
        let erase2 = Agent::new_ref(AgentType::Ε);
        // SAFETY: (erase_node, 0) is unlinked
        Agent::unsafe_link_to_target_of(token, (erase, 0), (target, 1));
        // SAFETY: (erase_node_2, 0) is unlinked
        Agent::unsafe_link_to_target_of(token, (&erase2, 0), (target, 2));
    }

    /// Apply an interaction rule to two nodes connected at their principal ports
    fn interact_pair<'a>(
        token: &'a mut GhostToken<'id>,
        a: &'a AgentRef<'id>,
        b: &'a AgentRef<'id>,
    ) {
        let a_type = a.borrow(token).agent_type;
        let b_type = b.borrow(token).agent_type;
        match (a_type, b_type) {
            // root nodes cannot interact, since they have no principal port
            (AgentType::Root, _) => panic!("attempted to interact with a root node"),
            (_, AgentType::Root) => panic!("attempted to interact with a root node"),
            // common agents annihilate
            (AgentType::Γ(_), AgentType::Γ(_)) => Agent::annihilate2(token, a, b),
            (AgentType::Δ(m), AgentType::Δ(n)) => {
                if m == n {
                    Agent::annihilate2(token, a, b)
                } else {
                    Agent::commute2(token, a, b)
                }
            }
            (AgentType::Ε, AgentType::Ε) => {
                Agent::destroy(token, a);
                Agent::destroy(token, b)
            }
            // γ and δ commute past each other
            (AgentType::Γ(_), AgentType::Δ(_)) => Agent::commute2(token, a, b),
            (AgentType::Δ(_), AgentType::Γ(_)) => Agent::commute2(token, a, b),
            // ε erases
            (AgentType::Γ(_) | AgentType::Δ(_), AgentType::Ε) => Agent::erase2(token, a, b),
            (AgentType::Ε, AgentType::Γ(_) | AgentType::Δ(_)) => Agent::erase2(token, b, a),
        }
    }
}

pub struct INet<'id> {
    root: AgentRef<'id>,
}

impl<'id> INet<'id> {
    pub fn compile(token: &mut GhostToken<'id>, term: &Term) -> Self {
        use cons_list::ConsList;
        fn new_agent<'id>(agent_type: AgentType) -> AgentRef<'id> {
            Arc::new(GhostCell::new(Agent::new(agent_type)))
        }
        fn go<'id>(
            token: &mut GhostToken<'id>,
            term: &Term,
            scope: &ConsList<PortRef<'id, '_>>,
            parent_port: PortRef<'id, '_>,
            δ_tag: &mut usize,
        ) {
            match term {
                Term::Lam(body) => {
                    debug_println!("translating lambda: {:?}", term);
                    let λ = new_agent(AgentType::Γ(ΓTag::Λ));
                    Agent::unsafe_link(token, (&λ, 0), parent_port);
                    // the argument should be unused by default
                    let ε = new_agent(AgentType::Ε);
                    Agent::unsafe_link(token, (&λ, 1), (&ε, 0));
                    go(token, body, &scope.append((&λ, 1)), (&λ, 2), δ_tag);
                }
                Term::App(f, x) => {
                    debug_println!("translating application: {:?}", term);
                    let app = new_agent(AgentType::Γ(ΓTag::Α));
                    Agent::unsafe_link(token, (&app, 2), parent_port);
                    go(token, f, scope, (&app, 0), δ_tag);
                    go(token, x, scope, (&app, 1), δ_tag);
                }
                Term::Var(n) => {
                    debug_println!("translating var: {:?}", term);
                    // bounds sanity check: scope with index 0 has length 1; if scope has length 0,
                    // then we don't have variable 0
                    if scope.len() <= *n {
                        panic!("Invalid debruijn term during inet translation");
                    }
                    let λ: PortRef<'id, '_> = *scope.iter().nth(*n).unwrap();
                    // SAFETY: the lambda's variable is always initialized to an ε-node to start
                    // with.
                    let target = Agent::unsafe_take(token, λ).unwrap();
                    if matches!(target.0.borrow(token).agent_type, AgentType::Ε) {
                        // SAFETY: abs is relinked in the next line
                        // unlink the epsilon and GC it
                        Agent::unsafe_take(token, (&target.0, target.1));
                        // SAFETY: parent port is unlinked
                        Agent::unsafe_link(token, λ, parent_port);
                    } else {
                        let δ = new_agent(AgentType::Δ(*δ_tag));
                        *δ_tag += 1;
                        // SAFETY: (dup, 0) is unlinked by default
                        // SAFETY: abs was unlinked before matching
                        Agent::unsafe_link(token, (&δ, 0), λ);
                        // SAFETY: (dup, 1) is unlinked by default
                        // SAFETY: parent_port is unlinked
                        // link the new usage to the dup
                        Agent::unsafe_link(token, (&δ, 1), parent_port);
                        // SAFETY: (dup, 2) is unlinked by default
                        // SAFETY: target_port used to point to abs, which was relinked
                        // link the old usage to the dup
                        Agent::unsafe_link(token, (&δ, 2), (&target.0, target.1));
                    }
                }
            }
        }
        let mut δ_tag: usize = 1; // arbitrary
        let root = Arc::new(GhostCell::new(Agent::new(AgentType::Root)));
        go(token, term, &ConsList::new(), (&root, 1), &mut δ_tag);
        INet { root }
    }

    pub fn decompile(&self, token: &GhostToken<'id>) -> Term {
        use cons_list::ConsList;
        fn go<'id, 'a>(
            token: &'a GhostToken<'id>,
            port: PortRef<'id, 'a>,
            depth: usize,
            depth_map: &mut HashMap<AgentId, usize>,
            exit: &ConsList<usize>,
        ) -> Term {
            let agent = port.0.borrow(token);
            depth_map.entry(agent.id).or_insert(depth);
            match agent.agent_type {
                AgentType::Root => {
                    if port.1 == 1 {
                        let target = agent
                            .target(1)
                            .expect("encountered empty root while translating inet to lambda");
                        go(token, target, depth, depth_map, exit)
                    } else {
                        panic!("visited invalid port of root while translating inet to lambda");
                    }
                }
                AgentType::Γ(ΓTag::Λ) => {
                    if port.1 == 0 {
                        // first visit - visit body next
                        let body = agent
                            .target(2)
                            .expect("λ agent missing a body while translating inet to lambda");
                        let res = go(token, body, depth + 1, depth_map, exit);
                        Term::Lam(Box::new(res))
                    } else if port.1 == 1 {
                        // variable
                        let first_depth: usize = *depth_map.get(&agent.id).expect(
                            "depth map missing inserted agent id while translating inet to lambda",
                        );
                        Term::Var(depth - first_depth - 1)
                    } else {
                        panic!("port 2 of a λ agent visited while translating inet to lambda");
                    }
                }
                AgentType::Γ(ΓTag::Α) => {
                    if port.1 == 2 {
                        let f = agent
                            .target(0)
                            .expect("α agent missing a function while translating inet to lambda");
                        let x = agent
                            .target(1)
                            .expect("α agent missing an argument while translating inet to lambda");
                        let f_term = go(token, f, depth, depth_map, exit);
                        let x_term = go(token, x, depth, depth_map, exit);
                        Term::App(Box::new(f_term), Box::new(x_term))
                    } else {
                        panic!(
                            "visited an invalid port of α agent while translating inet to lambda"
                        );
                    }
                }
                AgentType::Δ(_) => {
                    let (next_port_num, new_exit) = if port.1 == 0 {
                        let next_port_num = *exit.head().expect(
                            "visited the principal of a δ agent before visiting the children",
                        );
                        (next_port_num, exit.tail())
                    } else {
                        (0, exit.append(port.1))
                    };
                    let next_port = agent
                        .target(next_port_num)
                        .expect("δ agent missing an argument while translating inet to lambda");
                    go(token, next_port, depth, depth_map, &new_exit)
                }
                AgentType::Ε => {
                    panic!("ε agent visited when translating inet to lambda");
                }
            }
        }
        go(
            token,
            (&self.root, 1),
            0,
            &mut HashMap::new(),
            &ConsList::new(),
        )
    }

    fn reduce(&self, token: &mut GhostToken<'id>) {
    }
}

pub fn reduce_lambda(term: &Term) -> Term {
    GhostToken::new(|mut token| {
        let net = INet::compile(&mut token, term);
        net.reduce(&mut token);
        net.decompile(&token)
    })
}
