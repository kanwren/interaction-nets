use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

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
pub type Port<'id> = (AgentRef<'id>, usize);
pub type PortRef<'id, 'a> = (&'a AgentRef<'id>, usize);
const MAX_PORTS: usize = 3;
pub type AgentRef<'id> = Arc<GhostCell<'id, Agent<'id>>>;

type AgentId = usize;
static AGENT_ID_COUNTER: AtomicUsize = AtomicUsize::new(1);
fn new_agent_id() -> AgentId { AGENT_ID_COUNTER.fetch_add(1, Ordering::Relaxed) }

pub struct Agent<'id> {
    pub agent_type: AgentType,
    pub ports: [Option<Port<'id>>; MAX_PORTS],
    id: AgentId,
}

impl<'id> Agent<'id> {
    pub fn new(agent_type: AgentType) -> Self {
        Agent {
            agent_type,
            id: new_agent_id(),
            ports: Default::default(),
        }
    }

    /// Like [unlink], but unidirectional. Returns the old port. Assumes that the old
    /// target of the node will be unlinked; if not, behavior is undefined.
    fn unsafe_take<'a>(
        token: &'a mut GhostToken<'id>,
        port: PortRef<'id, 'a>,
    ) -> Option<Port<'id>> {
        debug_println!("unlinking: ({:?}, {:?})", port.0.borrow(token).agent_type, port.1);
        port.0.borrow_mut(token).ports[port.1].take()
    }

    /// Unlink the port of the given agent and its target
    pub fn unlink<'a>(
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

    /// Link the two agents at the specified ports. Note that the old targets of these ports are
    /// unlinked.
    pub fn link<'a>(token: &'a mut GhostToken<'id>, p1: PortRef<'id, 'a>, p2: PortRef<'id, 'a>) {
        Agent::unlink(token, p1);
        Agent::unlink(token, p2);
        Agent::unsafe_link(token, p1, p2);
    }

    /// Link port `p1` to port `p2`, but not the other way around.
    pub fn unsafe_uni_link<'a>(
        token: &'a mut GhostToken<'id>,
        p1: PortRef<'id, 'a>,
        p2: PortRef<'id, 'a>,
    ) {
        debug_println!("linking: ({:?}, {:?}) to ({:?}, {:?})", p1.0.borrow(token).agent_type, p1.1, p2.0.borrow(token).agent_type, p2.1);
        p1.0.borrow_mut(token).ports[p1.1] = Some((Arc::clone(p2.0), p2.1));
    }

    /// Link the two agents at the specified ports, but do not unlink the ports first. If the ports
    /// hvae old targets and they are not relinked afterwards, behavior is undefined.
    pub fn unsafe_link<'a>(
        token: &'a mut GhostToken<'id>,
        p1: PortRef<'id, 'a>,
        p2: PortRef<'id, 'a>,
    ) {
        Agent::unsafe_uni_link(token, p1, p2);
        Agent::unsafe_uni_link(token, p2, p1);
    }

    /// Unlinks the given ports and links their old targets together.
    pub fn relink<'a>(token: &'a mut GhostToken<'id>, p1: PortRef<'id, 'a>, p2: PortRef<'id, 'a>) {
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

    // Apply the annihilation rule to two nodes of the same type that both have arity 2 (in
    // particular, γ and δ) interacting at their principal ports.
    // Does not check these preconditions! This should be used as a helper in interactions only.
    fn unsafe_annihilate2<'a>(
        token: &'a mut GhostToken<'id>,
        a: &'a AgentRef<'id>,
        b: &'a AgentRef<'id>,
    ) {
        Agent::unlink(token, (a, 0)); // unlink BOTH principal ports (for GC reasons)
        Agent::relink(token, (a, 1), (b, 1));
        Agent::relink(token, (a, 2), (b, 2));
        // all ports on a, b should be unlinked
    }

    // Apply the commuting rule to two nodes of different types that both have arity 2 (in
    // particular, γ and δ) interacting at their principal ports.
    // Does not check these preconditions! This should be used as a helper in interactions only.
    fn commute2<'a>(token: &'a mut GhostToken<'id>, a: &'a AgentRef<'id>, b: &'a AgentRef<'id>) {
        // link p1 to the target of p2, unlinking p2 in the process
        fn unsafe_link_to_target_of<'id, 'a>(
            token: &'a mut GhostToken<'id>,
            p1: PortRef<'id, 'a>,
            p2: PortRef<'id, 'a>,
        ) {
            // SAFETY: `p2_target` is relinked in the next line.
            if let Some(p2_target) = Agent::unsafe_take(token, p2) {
                Agent::unsafe_link(token, p1, (&p2_target.0, p2_target.1));
            } else {
                // SAFETY: each case must be verified below.
                Agent::unsafe_take(token, p1);
            }
        }
        let a2: AgentRef = Arc::new(GhostCell::new(Agent::new(a.borrow(token).agent_type)));
        let b2: AgentRef = Arc::new(GhostCell::new(Agent::new(b.borrow(token).agent_type)));
        // SAFETY: (b, 0) used to be linked to (a, 0), which is relinked in line 2.
        // SAFETY: target of (a, 1) used to be linked to (a, 1), which is unlinked here and relinked in line 3.
        unsafe_link_to_target_of(token, (b, 0), (a, 1));
        // SAFETY: (a, 0) used to be linked to (b, 0), which was relinked in line 1.
        // SAFETY: target of (b, 1) used to be linked to (b, 1), which is unlinked here and relinked in line 3.
        unsafe_link_to_target_of(token, (a, 0), (b, 1));
        // SAFETY: (b, 1) was unlinked in line 2.
        // SAFETY: (a, 1) was unlinked in line 1
        Agent::unsafe_link(token, (b, 1), (a, 1));
        // SAFETY: (b2, 0) is unlinked by default.
        // SAFETY: target of (a, 2) used to be linked to (a, 2), which is unlinked here and relinked in line 6.
        unsafe_link_to_target_of(token, (&b2, 0), (a, 2));
        // SAFETY: (a2, 0) is unlinked by default.
        // SAFETY: target of (b, 2) used to be linked to (b, 2), which is unlinked here and relinked in line 6.
        unsafe_link_to_target_of(token, (&a2, 0), (b, 2));
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

    /// Unlink all ports of an agent and destroy it
    pub fn destroy<'a>(token: &'a mut GhostToken<'id>, a: &'a AgentRef<'id>) {
        for i in 0..MAX_PORTS {
            Agent::unlink(token, (a, i));
        }
    }
}

pub struct INet<'id> {
    root: AgentRef<'id>,
}

impl<'id> INet<'id> {
    pub fn from_lambda(token: &mut GhostToken<'id>, term: &Term) -> Self {
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
                    let (target, target_port_num) = Agent::unsafe_take(token, λ).unwrap();
                    if matches!(target.borrow(token).agent_type, AgentType::Ε) {
                        // SAFETY: abs is relinked in the next line
                        // unlink the epsilon and GC it
                        Agent::unsafe_take(token, (&target, target_port_num));
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
                        Agent::unsafe_link(token, (&δ, 2), (&target, target_port_num));
                    }
                }
            }
        }
        let mut δ_tag: usize = 1; // arbitrary
        let root = Arc::new(GhostCell::new(Agent::new(AgentType::Root)));
        go(token, term, &ConsList::new(), (&root, 1), &mut δ_tag);
        INet { root }
    }

    pub fn to_lambda(token: &GhostToken<'id>, net: &Self) -> Term {
        use cons_list::ConsList;
        fn go<'id, 'a>(
            token: &'a GhostToken<'id>,
            port: PortRef<'id, 'a>,
            depth: usize,
            depth_map: &mut HashMap<AgentId, usize>,
            exit: &ConsList<usize>,
        ) -> Term {
            let agent = port.0.borrow(token);
            if !depth_map.contains_key(&agent.id) {
                depth_map.insert(agent.id, depth);
            }
            match agent.agent_type {
                AgentType::Root => {
                    if port.1 == 1 {
                        if let Some((ref target, target_port_num)) = agent.ports[1] {
                            go(token, (target, target_port_num), depth, depth_map, exit)
                        } else {
                            panic!("encountered empty root while translating inet to lambda");
                        }
                    } else {
                        panic!("visited invalid port of root while translating inet to lambda");
                    }
                },
                AgentType::Γ(ΓTag::Λ) => {
                    if port.1 == 0 {
                        // first visit - visit body next
                        if let Some((ref body, body_port_num)) = agent.ports[2] {
                            let res = go(token, (body, body_port_num), depth + 1, depth_map, exit);
                            Term::Lam(Box::new(res))
                        } else {
                            panic!("λ agent missing a body while translating inet to lambda - this should not be possible");
                        }
                    } else if port.1 == 1 {
                        // variable
                        let first_depth: usize = *depth_map.get(&agent.id).expect("depth map missing inserted agent id while translating inet to lambda");
                        Term::Var(depth - first_depth - 1)
                    } else {
                        panic!("port 2 of a λ agent visited while translating inet to lambda - this should not be possible");
                    }
                },
                AgentType::Γ(ΓTag::Α) => {
                    if port.1 == 2 {
                        if let Some((ref f, f_port_num)) = agent.ports[0] {
                            if let Some((ref x, x_port_num)) = agent.ports[1] {
                                let f_term = go(token, (f, f_port_num), depth, depth_map, exit);
                                let x_term = go(token, (x, x_port_num), depth, depth_map, exit);
                                Term::App(Box::new(f_term), Box::new(x_term))
                            } else {
                                panic!("α agent missing an argument while translating inet to lambda - this should not be possible");
                            }
                        } else {
                            panic!("α agent missing a function while translating inet to lambda - this should not be possible");
                        }
                    } else {
                        panic!("visited an invalid port of α agent while translating inet to lambda - this should not be possible");
                    }
                },
                AgentType::Δ(_) => {
                    let (next_port, new_exit) = if port.1 == 0 {
                        let next_port = *exit.head().expect("visited the principal of a δ agent before visiting the children - this should not be possible");
                        (next_port, exit.tail())
                    } else {
                        (0, exit.append(port.1))
                    };
                    if let Some((ref next_port, next_port_num)) = agent.ports[next_port] {
                        go(token, (next_port, next_port_num), depth, depth_map, &new_exit)
                    } else {
                        panic!("δ agent missing an argument while translating inet to lambda - this should not be possible");
                    }
                },
                AgentType::Ε => {
                    panic!("ε agent visited when translating inet to lambda - this should not be possible");
                },
            }
        }
        go(token, (&net.root, 1), 0, &mut HashMap::new(), &ConsList::new())
    }
}
