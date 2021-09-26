#![allow(dead_code)]
use super::term::*;
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::state::{State, StateMachine};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;

type RState = Rc<State>;

/**
 * implementation of symbolic finite state transducer (SFST)
 */
pub struct SymFST<S: FunctionTerm> {
    states: HashSet<RState>,
    initial_state: RState,
    final_states: HashSet<RState>,
    transition: HashMap<(RState, Rc<S::Underlying>), (RState, Vec<Rc<S>>)>,
}
impl<S: FunctionTerm> SymFST<S> {
    pub fn run(
        &self,
        input: &[<S::Underlying as BoolAlg>::Domain],
    ) -> Vec<Vec<<S::Underlying as BoolAlg>::Domain>>
    where
        <S::Underlying as BoolAlg>::Domain: Copy,
    {
        let mut input = input.iter();
        let mut possibilities = vec![];
        possibilities.push((Rc::clone(&self.initial_state), vec![]));

        while let Some(c) = input.next() {
            possibilities = possibilities
                .iter()
                .flat_map(|(state, w)| {
                    self.transition
                        .iter()
                        .filter_map(|((s1, phi), (s2, fs))| {
                            if state == s1 && phi.denotate(c) {
                                let mut w = w.clone();
                                w.extend(fs.iter().map(|f| *f.apply(c)));
                                Some((Rc::clone(s2), w))
                            } else {
                                None
                            }
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        }

        possibilities
            .into_iter()
            .filter_map(|(s, w)| {
                if self.final_states.contains(&s) {
                    Some(w)
                } else {
                    None
                }
            })
            .collect()
    }
}
impl<'a, T: PartialOrd + Eq + Copy + Hash> SymFST<Lambda<Predicate<'a, T>>> {
    pub fn new(
        states: HashSet<RState>,
        initial_state: RState,
        final_states: HashSet<RState>,
        transition: HashMap<(RState, Rc<Predicate<'a, T>>), (RState, Vec<Rc<Lambda<Predicate<'a, T>>>>)>,
    ) -> SymFST<Lambda<Predicate<'a, T>>> {
        let mut fst = SymFST {
            states,
            initial_state,
            final_states,
            transition,
        };
        fst.minimize();
        fst
    }
}
impl<'a, T: PartialOrd + Eq + Copy + Hash> StateMachine for SymFST<Lambda<Predicate<'a, T>>> {
    type Source = (RState, Rc<Predicate<'a, T>>);
    type Target = (RState, Vec<Rc<Lambda<Predicate<'a, T>>>>);
    type FinalSet = HashSet<RState>;

    fn states(&self) -> &HashSet<Rc<State>> {
        &self.states
    }
    fn states_mut(&mut self) -> &mut HashSet<Rc<State>> {
        &mut self.states
    }

    fn initial_state(&self) -> &Rc<State> {
        &self.initial_state
    }
    fn initial_state_mut(&mut self) -> &mut Rc<State> {
        &mut self.initial_state
    }

    fn final_set(&self) -> &Self::FinalSet {
        &self.final_states
    }
    fn final_set_mut(&mut self) -> &mut Self::FinalSet {
        &mut self.final_states
    }
    fn final_set_filter_by_states(&self, reachables: &HashSet<Rc<State>>) -> Self::FinalSet {
        self.final_states
            .intersection(reachables)
            .map(|final_state| Rc::clone(final_state))
            .collect()
    }

    fn source_to_state(s: &Self::Source) -> &Rc<State> {
        &s.0
    }
    fn target_to_state(t: &Self::Target) -> &Rc<State> {
        &t.0
    }
    fn clone_source(s: &Self::Source) -> Self::Source {
        (Rc::clone(&s.0), Rc::clone(&s.1))
    }
    fn clone_target(t: &Self::Target) -> Self::Target {
        (Rc::clone(&t.0), t.1.iter().map(|out| Rc::clone(out)).collect())
    }

    fn transition(&self) -> &HashMap<Self::Source, Self::Target> {
        &self.transition
    }
    fn transition_mut(&mut self) -> &mut HashMap<Self::Source, Self::Target> {
        &mut self.transition
    }
}
