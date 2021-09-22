#![allow(dead_code)]
use super::term::*;
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::state::State;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;

/**
 * implementation of symbolic streaming string transducer (SSST)
 */
struct SymSST<'a, T: BoolAlg, S: FunctionTerm> {
  states: HashSet<Rc<State>>,
  initial_state: Rc<State>,
  output_function: HashMap<Rc<State>, Rc<Vec<OutputComp<'a, T::Domain>>>>,
  transition: HashMap<
    (Rc<State>, Rc<T>),
    (
      Rc<State>,
      HashMap<Rc<Variable<'a>>, Rc<Vec<UpdateComp<'a, S>>>>,
    ),
  >,
}
impl<'a, T: PartialOrd + Copy + Eq + Hash> SymSST<'a, Predicate<'a, T>, Lambda<Predicate<'a, T>>> {
  fn new(
    states: HashSet<Rc<State>>,
    initial_state: Rc<State>,
    output_function: HashMap<Rc<State>, Rc<Vec<OutputComp<'a, T>>>>,
    transition: HashMap<
      (Rc<State>, Rc<Predicate<'a, T>>),
      (
        Rc<State>,
        HashMap<Rc<Variable<'a>>, Rc<Vec<UpdateComp<'a, Lambda<Predicate<'a, T>>>>>>,
      ),
    >,
  ) -> SymSST<'a, Predicate<'a, T>, Lambda<Predicate<'a, T>>> {
    SymSST {
      states,
      initial_state,
      output_function,
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
      .filter_map(|((state, phi), (next, alpha))| {
        if self.states.contains(state) && self.states.contains(next) {
          Some((
            (Rc::clone(state), Rc::clone(phi)),
            (
              Rc::clone(next),
              alpha
                .iter()
                .map(|(x, alpha_x)| (Rc::clone(x), Rc::clone(alpha_x)))
                .collect(),
            ),
          ))
        } else {
          None
        }
      })
      .collect();
    self.output_function = self
      .output_function
      .iter()
      .filter_map(|(state, out)| {
        if self.states.contains(state) {
          Some((Rc::clone(state), Rc::clone(out)))
        } else {
          None
        }
      })
      .collect();
  }
}
