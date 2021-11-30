use super::term::*;
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::state::{State, StateMachine};
use std::{
  collections::{HashMap, HashSet},
  fmt::Debug,
  hash::Hash,
  rc::Rc,
};

type RState = Rc<State>;

/**
 * implementation of symbolic finite state transducer (SFST)
 */
#[derive(Debug, PartialEq)]
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
          self
            .transition
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
impl<T> SymFST<Lambda<Predicate<T>>>
where
  T: PartialOrd + Ord + Copy + PartialEq + Eq + Hash + Debug,
{
  pub fn new(
    states: HashSet<RState>,
    initial_state: RState,
    final_states: HashSet<RState>,
    transition: HashMap<(RState, Rc<Predicate<T>>), (RState, Vec<Rc<Lambda<Predicate<T>>>>)>,
  ) -> SymFST<Lambda<Predicate<T>>> {
    SymFST {
      states,
      initial_state,
      final_states,
      transition,
    }
    .minimize()
  }
}
impl<T> StateMachine for SymFST<Lambda<Predicate<T>>>
where
  T: PartialOrd + Ord + Copy + PartialEq + Eq + Hash + Debug,
{
  type Source = (RState, Rc<Predicate<T>>);
  type Target = (RState, Vec<Rc<Lambda<Predicate<T>>>>);
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
    self
      .final_states
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

  fn transition(&self) -> &HashMap<Self::Source, Self::Target> {
    &self.transition
  }
  fn transition_mut(&mut self) -> &mut HashMap<Self::Source, Self::Target> {
    &mut self.transition
  }
}

pub type Transducer<T> = SymFST<Lambda<Predicate<T>>>;
