use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

use ghost_cell::{GhostCell, GhostToken};

use crate::lambda::DebruijnTerm;

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
type PortNum = usize;
type Port<'id> = (AgentRef<'id>, PortNum);
type PortRef<'id, 'a> = (&'a AgentRef<'id>, PortNum);
const MAX_PORTS: usize = 3;
type AgentRef<'id> = Rc<GhostCell<'id, Agent<'id>>>;

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

    // regenerate a node ID, for example if a node is reused for an interaction
    fn refresh_id(&mut self) {
        self.id = AgentId::new();
    }

    fn new_ref(agent_type: AgentType) -> AgentRef<'id> {
        Rc::new(GhostCell::new(Agent::new(agent_type)))
    }

    fn target<'a>(&'a self, port_num: PortNum) -> Option<PortRef<'id, 'a>> {
        self.ports[port_num].as_ref().map(|t| (&t.0, t.1))
    }

    fn unchecked_target<'a>(&'a self, port_num: PortNum) -> PortRef<'id, 'a> {
        let t = self.ports[port_num]
            .as_ref()
            .expect("agent port is missing target which was expected to be present");
        (&t.0, t.1)
    }

    /// Like [unlink], but unidirectional. Returns the old port. Assumes that the old
    /// target of the node will be unlinked; if not, behavior is undefined.
    fn unsafe_take<'a>(
        token: &'a mut GhostToken<'id>,
        port: PortRef<'id, 'a>,
    ) -> Option<Port<'id>> {
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
        p1.0.borrow_mut(token).ports[p1.1] = Some((Rc::clone(p2.0), p2.1));
        p2.0.borrow_mut(token).ports[p2.1] = Some((Rc::clone(p1.0), p1.1));
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

    /// Apply the commuting rule to two nodes of different types that both have arity 2 (in
    /// particular, γ and δ) interacting at their principal ports. Does not check these
    /// preconditions! This should be used as a helper in interactions only.
    ///
    /// Assumes that the principal ports have already been unlinked (by interact_pair).
    fn commute2<'a>(token: &'a mut GhostToken<'id>, a: &'a AgentRef<'id>, b: &'a AgentRef<'id>) {
        let a2: AgentRef = Agent::new_ref(a.borrow(token).agent_type);
        let b2: AgentRef = Agent::new_ref(b.borrow(token).agent_type);
        // SAFETY: we assume the principal ports are unlinked. if not, then (b, 0) used to be linked to (a, 0), which is relinked in line 2.
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
        // a and b are reused, so their IDs must be regenerated
        a.borrow_mut(token).refresh_id();
        b.borrow_mut(token).refresh_id();
    }

    /// Applies the erasing rule on an arity-2 agent interacting with an ε agent at its principal
    /// port. Assumes that that exactly one of the nodes is an ε agent, and that they are already
    /// connected.
    ///
    /// Assumes that the principal ports have already been unlinked (by interact_pair).
    fn erase2<'a>(token: &'a mut GhostToken<'id>, a: &'a AgentRef<'id>, b: &'a AgentRef<'id>) {
        let (erase, target) = if a.borrow(token).agent_type == AgentType::Ε {
            (a, b)
        } else {
            (b, a)
        };
        let erase2 = Agent::new_ref(AgentType::Ε);
        // SAFETY: (erase_node, 0) is unlinked
        Agent::unsafe_link_to_target_of(token, (erase, 0), (target, 1));
        // SAFETY: (erase_node_2, 0) is unlinked
        Agent::unsafe_link_to_target_of(token, (&erase2, 0), (target, 2));
        // erase is reused, so its ID must be regenerated, while target is eliminated
        erase.borrow_mut(token).refresh_id();
    }

    /// Apply an interaction rule to two nodes connected at their principal ports.
    /// nodes
    fn interact_pair(token: &mut GhostToken<'id>, a: &AgentRef<'id>) {
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
        let b = {
            // take the target of a's principle port as the second agent in the pair
            let a_target = a.borrow_mut(token).ports[0]
                .take()
                .expect("found unconnected principle port during interaction");
            // the interaction should take place at b's principal port
            assert!(a_target.1 == 0);
            a_target.0
        };
        let a_type = a.borrow(token).agent_type;
        let b_type = b.borrow(token).agent_type;
        match (a_type, b_type) {
            // root nodes cannot interact, since they have no principal port
            (AgentType::Root, _) | (_, AgentType::Root) => panic!("attempted to interact with a root node"),
            // common agents annihilate
            (AgentType::Γ(_), AgentType::Γ(_)) => {
                relink(token, (a, 1), (&b, 1));
                relink(token, (a, 2), (&b, 2));
            },
            (AgentType::Δ(m), AgentType::Δ(n)) => {
                if m == n {
                    relink(token, (a, 1), (&b, 1));
                    relink(token, (a, 2), (&b, 2));
                } else {
                    Agent::commute2(token, a, &b)
                }
            }
            // γ and δ commute past each other
            (AgentType::Γ(_), AgentType::Δ(_)) | (AgentType::Δ(_), AgentType::Γ(_)) => Agent::commute2(token, a, &b),
            // ε erases
            (AgentType::Γ(_) | AgentType::Δ(_), AgentType::Ε) | (AgentType::Ε, AgentType::Γ(_) | AgentType::Δ(_)) => Agent::erase2(token, a, &b),
            (AgentType::Ε, AgentType::Ε) => {
                Agent::unlink(token, (a, 0));
                Agent::unlink(token, (&b, 0));
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Stats {
    pub reductions: usize,
    pub betas: usize,
}

pub struct INet<'id> {
    root: AgentRef<'id>,
}

impl<'id> INet<'id> {
    pub fn compile(token: &mut GhostToken<'id>, term: &DebruijnTerm) -> Self {
        use cons_list::ConsList;
        fn new_agent<'id>(agent_type: AgentType) -> AgentRef<'id> {
            Rc::new(GhostCell::new(Agent::new(agent_type)))
        }
        fn go<'id>(
            token: &mut GhostToken<'id>,
            term: &DebruijnTerm,
            scope: &ConsList<PortRef<'id, '_>>,
            parent_port: PortRef<'id, '_>,
            δ_tag: &mut usize,
        ) {
            match term {
                DebruijnTerm::Lam(body) => {
                    let λ = new_agent(AgentType::Γ(ΓTag::Λ));
                    Agent::unsafe_link(token, (&λ, 0), parent_port);
                    // the argument should be unused by default
                    let ε = new_agent(AgentType::Ε);
                    Agent::unsafe_link(token, (&λ, 1), (&ε, 0));
                    go(token, body, &scope.append((&λ, 1)), (&λ, 2), δ_tag);
                }
                DebruijnTerm::App(f, x) => {
                    let app = new_agent(AgentType::Γ(ΓTag::Α));
                    Agent::unsafe_link(token, (&app, 2), parent_port);
                    go(token, f, scope, (&app, 0), δ_tag);
                    go(token, x, scope, (&app, 1), δ_tag);
                }
                DebruijnTerm::Var(n) => {
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
        let root = Rc::new(GhostCell::new(Agent::new(AgentType::Root)));
        go(token, term, &ConsList::new(), (&root, 1), &mut δ_tag);
        INet { root }
    }

    // TODO: this is likely to stack overflow on large numbers, consider trampolining
    pub fn decompile(&self, token: &GhostToken<'id>) -> DebruijnTerm {
        use cons_list::ConsList;
        fn go<'id, 'a>(
            token: &'a GhostToken<'id>,
            port: PortRef<'id, 'a>,
            depth: usize,
            depth_map: &mut HashMap<AgentId, usize>,
            exit: &ConsList<PortNum>,
        ) -> DebruijnTerm {
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
                        DebruijnTerm::Lam(Box::new(res))
                    } else if port.1 == 1 {
                        // variable
                        let first_depth: usize = *depth_map.get(&agent.id).expect(
                            "depth map missing inserted agent id while translating inet to lambda",
                        );
                        DebruijnTerm::Var(depth - first_depth - 1)
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
                        DebruijnTerm::App(Box::new(f_term), Box::new(x_term))
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

    fn reduce(&self, token: &mut GhostToken<'id>) -> Stats {
        let mut reductions = 0;
        let mut betas = 0;

        let mut exit_ports = HashMap::<AgentId, PortNum>::new();
        let mut frozen_agents = HashSet::<AgentId>::new();
        // TODO: see if this can be a Vec<PortRef<'id, '_>> instead
        let mut visit_stack = vec![(Rc::clone(&self.root), 1)];

        // used so we can take references to a cloned arc and use them interchangeably
        let mut exit_target;

        'visit_next_node: while let Some(visit) = visit_stack.pop() {
            let mut next = if let Some(next) = visit.0.borrow(token).target(visit.1) {
                next
            } else {
                continue;
            };
            loop {
                let next_agent = next.0.borrow(token);
                let next_agent_id = next_agent.id;
                let is_frozen = frozen_agents.contains(&next_agent.id);
                if is_frozen {
                    continue 'visit_next_node;
                }

                // TODO: Maia's implementation uses this; can we remove this and replace it
                // with the popped port?
                let prev = next_agent.unchecked_target(next.1);
                let prev_agent = prev.0.borrow(token);

                if next.1 == 0 {
                    if prev.1 == 0 {
                        // the nodes interact at the principal ports
                        reductions += 1;
                        if matches!(prev_agent.agent_type, AgentType::Γ(_))
                            && matches!(next_agent.agent_type, AgentType::Γ(_))
                        {
                            betas += 1;
                        }

                        // unwrap is safe here, since we couldn't have entered prev through its
                        // principal port, so it must have been placed in exit_ports below
                        let new_exit_target = {
                            let prev_agent = prev.0.borrow(token);
                            let exit_port_num = *exit_ports
                                .get(&prev_agent.id)
                                .expect("agent missing exit port during interaction");
                            let exit_target = prev_agent.target(exit_port_num).unwrap();
                            // TODO: try to remove this if possible
                            (Rc::clone(exit_target.0), exit_target.1)
                        };

                        // remove interacting nodes from state for GC reasons. they can't be
                        // frozen. they may have marked exit ports that might be revisisted, but
                        // those will be updated first, so that's not an issue.
                        exit_ports.remove(&prev_agent.id);
                        exit_ports.remove(&next_agent_id);

                        // TODO: try to remove this if possible
                        let prev_ref = Rc::clone(prev.0);
                        Agent::interact_pair(token, &prev_ref);
                        std::mem::drop(prev_ref);

                        exit_target = new_exit_target;
                        next = exit_target.0.borrow(token).unchecked_target(exit_target.1);
                    } else {
                        // the next node's principal port is pointing up, but isn't interacting.
                        // it can no longer interact, so it can safely be frozen
                        frozen_agents.insert(next_agent_id);
                        visit_stack.push((Rc::clone(next.0), 2));
                        visit_stack.push((Rc::clone(next.0), 1));
                        continue 'visit_next_node;
                    }
                } else {
                    // mark our exit path and continue to the next node, starting at the principal
                    // port (for semantic purposes)
                    exit_ports.insert(next_agent_id, next.1);
                    next = next.0.borrow(token).unchecked_target(0);
                }
            }
        }

        Stats {
            reductions,
            betas,
        }
    }
}

pub fn reduce_lambda(term: &DebruijnTerm) -> DebruijnTerm {
    GhostToken::new(|mut token| {
        let net = INet::compile(&mut token, term);
        net.reduce(&mut token);
        net.decompile(&token)
    })
}

pub fn reduce_lambda_with_stats(term: &DebruijnTerm) -> (DebruijnTerm, Stats) {
    GhostToken::new(|mut token| {
        let net = INet::compile(&mut token, term);
        let stats = net.reduce(&mut token);
        (net.decompile(&token), stats)
    })
}
