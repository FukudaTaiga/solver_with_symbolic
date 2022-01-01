use super::term::{FunctionTerm, FunctionTermImpl};
use crate::{
  boolean_algebra::{BoolAlg, Predicate},
  state::{State, StateMachine, self},
  util::FromChar
};
use std::{
  collections::{HashMap, HashSet},
  fmt::Debug,
};

type Source<B, S> = (S, B);
type Target<F, S> = (S, Vec<F>);

/** implementation of symbolic finite state transducer (SFST) */
#[derive(Debug, PartialEq, Clone)]
pub struct SymFST<D, B, F, S>
where
  B: BoolAlg<Domain = D>,
  F: FunctionTerm<Domain = D>,
  S: State,
{
  states: HashSet<S>,
  initial_state: S,
  final_states: HashSet<S>,
  transition: HashMap<Source<B, S>, Vec<Target<F, S>>>,
}
impl<D, B, F, S> SymFST<D, B, F, S>
where
  D: FromChar,
  B: BoolAlg<Domain = D>,
  F: FunctionTerm<Domain = D>,
  S: State,
{
  pub fn new(
    states: HashSet<S>,
    initial_state: S,
    final_states: HashSet<S>,
    transition: HashMap<Source<B, S>, Vec<Target<F, S>>>,
  ) -> Self {
    Self {
      states,
      initial_state,
      final_states,
      transition,
    }
    .minimize()
  }

  pub fn run<'a>(&self, input: impl IntoIterator<Item = &'a D>) -> Vec<Vec<D>>
  where
    D: 'a,
  {
    self.generalized_run(
      input.into_iter(),
      vec![(self.initial_state.clone(), vec![])],
      &mut |(_, w), c, (q, map)| {
        let mut w = w.clone();
        w.extend(map.into_iter().map(|f| D::clone(f.apply(c))));
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
impl<D, B, F, S> StateMachine for SymFST<D, B, F, S>
where
  D: FromChar,
  B: BoolAlg<Domain = D>,
  F: FunctionTerm<Domain = D>,
  S: State,
{
  type StateType = S;

  type BoolAlg = B;
  type Target = Target<F, S>;
  type FinalState = S;
  type FinalSet = HashSet<S>;

  fn empty() -> Self {
    let state = S::new();
    Self {
      states: HashSet::from([S::clone(&state)]),
      initial_state: state,
      final_states: HashSet::new(),
      transition: HashMap::new(),
    }
  }

  state::macros::impl_state_machine!(states, initial_state, final_states, transition);
}

pub type Transducer<T, S> = SymFST<T, Predicate<T>, FunctionTermImpl<T>, S>;
