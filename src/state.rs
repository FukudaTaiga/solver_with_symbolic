#![allow(dead_code)]
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;

static mut INTERNAL: u64 = 0;

#[derive(Debug, Hash, Eq, Clone)]
pub struct State {
    value: u64,
}
impl State {
    pub fn new() -> State {
        unsafe {
            INTERNAL += 1;
            State { value: INTERNAL }
        }
        //State {}
    }
}
impl PartialEq for State {
    fn eq(&self, other: &Self) -> bool {
        //std::ptr::eq(self, other)
        self.value == other.value
    }
}

//trait for state machine
pub trait StateMachine {
    /**
     * Source of the transition
     */
    type Source: Eq + Hash;
    /**
     * Target of the transition
     */
    type Target;
    /**
     * Determinizer of Output
     */
    type FinalSet;

    fn states(&self) -> &HashSet<Rc<State>>;
    fn states_mut(&mut self) -> &mut HashSet<Rc<State>>;

    fn initial_state(&self) -> &Rc<State>;
    fn initial_state_mut(&mut self) -> &mut Rc<State>;

    fn final_set(&self) -> &Self::FinalSet;
    fn final_set_mut(&mut self) -> &mut Self::FinalSet;
    fn final_set_filter_by_states(&self, reachables: &HashSet<Rc<State>>) -> Self::FinalSet;

    fn source_to_state(s: &Self::Source) -> &Rc<State>;
    fn target_to_state(t: &Self::Target) -> &Rc<State>;
    fn clone_source(s: &Self::Source) -> Self::Source;
    fn clone_target(t: &Self::Target) -> Self::Target;

    fn transition(&self) -> &HashMap<Self::Source, Self::Target>;
    fn transition_mut(&mut self) -> &mut HashMap<Self::Source, Self::Target>;

    fn minimize(&mut self) {
        let mut stack = vec![Rc::clone(&self.initial_state())];
        let mut reachables = vec![];

        while let Some(state) = stack.pop() {
            reachables.push(Rc::clone(&state));

            for (s, t) in self.transition() {
                if *Self::source_to_state(s) == state
                    && !reachables.contains(Self::target_to_state(t))
                {
                    stack.push(Rc::clone(&Self::target_to_state(t)));
                }
            }
        }

        *self.states_mut() = reachables.into_iter().collect();
        *self.transition_mut() = self
            .transition()
            .iter()
            .filter_map(|(s, t)| {
                if self.states().contains(Self::source_to_state(s))
                    && self.states().contains(Self::target_to_state(t))
                {
                    Some((Self::clone_source(s), Self::clone_target(t)))
                } else {
                    None
                }
            })
            .collect();
        *self.final_set_mut() = self.final_set_filter_by_states(self.states());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::RandomState;
    use std::iter::FromIterator;

    #[test]
    fn new_state_test() {
        let state_1 = State::new();
        let state_2 = State::new();

        assert_eq!(state_1, state_1);
        assert_ne!(state_1, state_2);
        assert_eq!(state_2, state_2);
        assert_ne!(state_2, state_1);
    }

    #[test]
    fn state_set_test() {
        let mut states100 = HashSet::new();
        for _ in 0..100 {
            states100.insert(State::new());
        }

        let state = State::new();
        let states1 = vec![state; 100];
        let states1 = HashSet::<_, RandomState>::from_iter(states1.iter());

        assert_eq!(states100.len(), 100);
        assert_eq!(states1.len(), 1);
    }
}
