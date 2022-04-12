use std::sync::Arc;

use ghost_cell::{GhostCell, GhostToken};

use crate::lambda::Term;

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
    /// port 2 is used instead.
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
const MAX_PORTS: usize = 3;
pub type AgentRef<'id> = Arc<GhostCell<'id, Agent<'id>>>;

pub struct Agent<'id> {
    pub agent_type: AgentType,
    pub ports: [Option<Port<'id>>; MAX_PORTS],
}

impl<'id> Agent<'id> {
    pub fn new(agent_type: AgentType) -> Self {
        Agent {
            agent_type,
            ports: Default::default(),
        }
    }

    /// Like [unlink], but unidirectional. Returns the old port.
    fn take<'a>(
        token: &'a mut GhostToken<'id>,
        agent: &'a AgentRef<'id>,
        i: usize,
    ) -> Option<Port<'id>> {
        agent.borrow_mut(token).ports[i].take()
    }

    /// Unlink the port of the given agent and its target
    pub fn unlink<'a>(token: &'a mut GhostToken<'id>, agent: &'a AgentRef<'id>, i: usize) {
        if let Some((target, target_port_num)) = Agent::take(token, agent, i) {
            Agent::take(token, &target, target_port_num);
        }
    }

    /// Link the two agents at the specified ports. Note that the old targets of these ports are
    /// unlinked.
    pub fn link<'a>(
        token: &'a mut GhostToken<'id>,
        p1: (&'a AgentRef<'id>, usize),
        p2: (&'a AgentRef<'id>, usize),
    ) {
        Agent::unlink(token, p1.0, p1.1);
        Agent::unlink(token, p2.0, p2.1);
        Agent::unsafe_link(token, p1, p2);
    }

    /// Link the two agents at the specified ports, but do not unlink the ports first. If the ports
    /// hvae old targets and they are not relinked afterwards, behavior is undefined.
    pub fn unsafe_link<'a>(
        token: &'a mut GhostToken<'id>,
        p1: (&'a AgentRef<'id>, usize),
        p2: (&'a AgentRef<'id>, usize),
    ) {
        p1.0.borrow_mut(token).ports[p1.1] = Some((Arc::clone(p2.0), p2.1));
        p2.0.borrow_mut(token).ports[p2.1] = Some((Arc::clone(p1.0), p1.1));
    }

    /// Unlinks the given ports and links their old targets together.
    fn relink<'a>(
        token: &'a mut GhostToken<'id>,
        p1: (&'a AgentRef<'id>, usize),
        p2: (&'a AgentRef<'id>, usize),
    ) {
        let a_dest: Option<Port<'id>> = Agent::take(token, p1.0, p1.1);
        let b_dest: Option<Port<'id>> = Agent::take(token, p2.0, p2.1);
        if let Some(a_dest1) = a_dest {
            if let Some(b_dest1) = b_dest {
                // SAFETY: a_dest and b_dest used to be linked to p1 and p2, which we already
                // unlinked above.
                Agent::unsafe_link(token, (&a_dest1.0, a_dest1.1), (&b_dest1.0, b_dest1.1));
            } else {
                Agent::unlink(token, &a_dest1.0, a_dest1.1);
            }
        } else if let Some(b_dest1) = b_dest {
            Agent::unlink(token, &b_dest1.0, b_dest1.1);
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
        Agent::unlink(token, a, 0); // unlink BOTH principal ports (for GC reasons)
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
            p1: (&'a AgentRef<'id>, usize),
            p2: (&'a AgentRef<'id>, usize),
        ) {
            if let Some(p2) = Agent::take(token, p2.0, p2.1) {
                Agent::unsafe_link(token, p1, (&p2.0, p2.1));
            } else {
                Agent::take(token, p1.0, p1.1);
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
}

pub struct INet<'id> {
    root: Agent<'id>,
}
