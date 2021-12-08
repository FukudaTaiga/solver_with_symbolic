use super::term::{FunctionTerm, FunctionTermImpl};
use crate::{
  boolean_algebra::BoolAlg,
  state::{StateImpl, StateMachine},
};
use std::{
  collections::{HashMap, HashSet},
  fmt::Debug,
  rc::Rc,
};

type Domain<F> = <<F as FunctionTerm>::Underlying as BoolAlg>::Domain;
type Source<F, S> = (S, Rc<<F as FunctionTerm>::Underlying>);
type Target<F, S> = (S, Vec<Rc<F>>);

/**
 * implementation of symbolic finite state transducer (SFST)
 */
#[derive(Debug, PartialEq, Clone)]
pub struct SymFST<F, S>
where
  F: FunctionTerm,
  S: StateImpl,
{
  states: HashSet<S>,
  initial_state: S,
  final_states: HashSet<S>,
  transition: HashMap<Source<F, S>, Target<F, S>>,
}
impl<F, S> SymFST<F, S>
where
  F: FunctionTerm + Clone,
  S: StateImpl,
{
  pub fn new(
    states: HashSet<S>,
    initial_state: S,
    final_states: HashSet<S>,
    transition: HashMap<Source<F, S>, Target<F, S>>,
  ) -> Self {
    Self {
      states,
      initial_state,
      final_states,
      transition,
    }
    .minimize()
  }

  pub fn run(&self, input: &[Domain<F>]) -> Vec<Vec<Domain<F>>> {
    let mut input = input.iter();
    let mut possibilities = vec![];
    possibilities.push((self.initial_state.clone(), vec![]));

    while let Some(c) = input.next() {
      possibilities = possibilities
        .into_iter()
        .flat_map(|(state, w)| {
          self
            .transition
            .iter()
            .filter_map(move |((p, phi), (q, map))| {
              if state == *p && phi.denotate(c) {
                let mut w = w.clone();
                w.extend(map.into_iter().map(|f| Domain::<F>::clone(f.apply(c))));
                Some((S::clone(q), w))
              } else {
                None
              }
            })
            .collect::<Vec<_>>()
        })
        .collect()
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
impl<F, S> StateMachine for SymFST<F, S>
where
  F: FunctionTerm + Clone,
  S: StateImpl,
{
  type StateType = S;

  type Source = Source<F, S>;
  type Target = Target<F, S>;
  type FinalSet = HashSet<S>;

  fn states(&self) -> &HashSet<Self::StateType> {
    &self.states
  }
  fn states_mut(&mut self) -> &mut HashSet<Self::StateType> {
    &mut self.states
  }

  fn initial_state(&self) -> &Self::StateType {
    &self.initial_state
  }
  fn initial_state_mut(&mut self) -> &mut Self::StateType {
    &mut self.initial_state
  }

  fn final_set(&self) -> &Self::FinalSet {
    &self.final_states
  }
  fn final_set_mut(&mut self) -> &mut Self::FinalSet {
    &mut self.final_states
  }
  fn final_set_filter_by_states<U: FnMut(&Self::StateType) -> bool>(
    &self,
    mut filter: U,
  ) -> Self::FinalSet {
    self
      .final_states
      .iter()
      .filter_map(|final_state| {
        if filter(final_state) {
          Some(final_state.clone())
        } else {
          None
        }
      })
      .collect()
  }

  fn source_to_state(s: &Self::Source) -> &Self::StateType {
    &s.0
  }
  fn target_to_state(t: &Self::Target) -> &Self::StateType {
    &t.0
  }

  fn transition(&self) -> &HashMap<Self::Source, Self::Target> {
    &self.transition
  }
  fn transition_mut(&mut self) -> &mut HashMap<Self::Source, Self::Target> {
    &mut self.transition
  }
  fn is_unreachable(s: &Self::Source) -> bool {
    s.1.is_bottom()
  }
}

pub type Transducer<T, S> = SymFST<FunctionTermImpl<T>, S>;
