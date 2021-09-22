#![allow(dead_code)]
use super::term::*;
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::state::State;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;

type RState = Rc<State>;

/**
 * implementation of symbolic finite state transducer (SFST)
 */
struct SymFST<T: BoolAlg, S: FunctionTerm> {
  states: HashSet<RState>,
  initial_state: RState,
  final_states: HashSet<RState>,
  transition: HashMap<(RState, Rc<T>), (RState, Rc<S>)>,
}
impl<'a, T: PartialOrd + Eq + Copy + Hash> SymFST<Predicate<'a, T>, Lambda<Predicate<'a, T>>> {
  fn new(
    states: HashSet<RState>,
    initial_state: RState,
    final_states: HashSet<RState>,
    transition: HashMap<(RState, Rc<Predicate<'a, T>>), (RState, Rc<Lambda<Predicate<'a, T>>>)>,
  ) -> SymFST<Predicate<'a, T>, Lambda<Predicate<'a, T>>> {
    SymFST {
      states,
      initial_state,
      final_states,
      transition,
    }
  }

  fn minimize(&mut self) {
    let mut stack = vec![Rc::clone(&self.initial_state)];
    let mut reachables = vec![];

    while let Some(state) = stack.pop() {
      reachables.push(Rc::clone(&state));

      for ((p, _), (q, _)) in &self.transition {
        if *p == state && !reachables.contains(&q) {
          stack.push(Rc::clone(&q));
        }
      }
    }

    self.states = reachables.into_iter().collect();
    self.transition = self
      .transition
      .iter()
      .filter_map(|((state, phi), (next, out))| {
        if self.states.contains(state) && self.states.contains(next) {
          Some((
            (Rc::clone(state), Rc::clone(phi)),
            (Rc::clone(next), Rc::clone(out)),
          ))
        } else {
          None
        }
      })
      .collect();
    self.final_states = self
      .final_states
      .intersection(&self.states)
      .map(|final_state| Rc::clone(final_state))
      .collect();
  }
}
