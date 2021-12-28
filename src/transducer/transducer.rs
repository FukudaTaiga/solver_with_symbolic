use super::term::{FunctionTerm, FunctionTermImpl};
use crate::{
  boolean_algebra::BoolAlg,
  state::{State, StateMachine},
};
use std::{
  collections::{HashMap, HashSet},
  fmt::Debug,
};

type Domain<F> = <<F as FunctionTerm>::Underlying as BoolAlg>::Domain;
type Source<F, S> = (S, <F as FunctionTerm>::Underlying);
type Target<F, S> = (S, Vec<F>);

/**
 * implementation of symbolic finite state transducer (SFST)
 */
#[derive(Debug, PartialEq, Clone)]
pub struct SymFST<F, S>
where
  F: FunctionTerm,
  S: State,
{
  states: HashSet<S>,
  initial_state: S,
  final_states: HashSet<S>,
  transition: HashMap<Source<F, S>, Vec<Target<F, S>>>,
}
impl<F, S> SymFST<F, S>
where
  F: FunctionTerm + Clone,
  S: State,
{
  pub fn new(
    states: HashSet<S>,
    initial_state: S,
    final_states: HashSet<S>,
    transition: HashMap<Source<F, S>, Vec<Target<F, S>>>,
  ) -> Self {
    Self {
      states,
      initial_state,
      final_states,
      transition,
    }
    .minimize()
  }

  pub fn run<'a>(&self, input: impl IntoIterator<Item = &'a Domain<F>>) -> Vec<Vec<Domain<F>>>
  where
    Domain<F>: 'a,
  {
    self.generalized_run(
      input,
      vec![(self.initial_state.clone(), vec![])],
      &mut |(_, w), c, (q, map)| {
        let mut w = w.clone();
        w.extend(map.into_iter().map(|f| Domain::<F>::clone(f.apply(c))));
        (S::clone(q), w)
      },
      |possibilities| {
        possibilities
          .into_iter()
          .filter_map(|(s, w)| (self.final_states.contains(&s)).then(|| w))
          .collect()
      },
    )
  }
}
impl<F, S> StateMachine for SymFST<F, S>
where
  F: FunctionTerm,
  S: State,
{
  type StateType = S;

  type BoolAlg = F::Underlying;
  type Target = Target<F, S>;
  type FinalState = S;
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

  fn transition(&self) -> &HashMap<(Self::StateType, Self::BoolAlg), Vec<Self::Target>> {
    &self.transition
  }
  fn transition_mut(
    &mut self,
  ) -> &mut HashMap<(Self::StateType, Self::BoolAlg), Vec<Self::Target>> {
    &mut self.transition
  }
}

pub type Transducer<T, S> = SymFST<FunctionTermImpl<T>, S>;
