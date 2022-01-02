use std::{
  collections::{HashMap, HashSet},
  fmt::Debug,
  hash::Hash,
  iter::FromIterator,
  rc::Rc,
  sync::atomic::{AtomicUsize, Ordering},
};

pub trait State: Debug + Eq + Ord + Hash + Clone {
  fn new() -> Self;
}
impl State for StateImpl {
  fn new() -> Self {
    StateImpl::new()
  }
}
impl State for Rc<StateImpl> {
  fn new() -> Self {
    Rc::new(StateImpl::new())
  }
}

static STATE_CNT: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Clone)]
pub struct StateImpl(usize);
impl StateImpl {
  pub fn new() -> StateImpl {
    StateImpl(STATE_CNT.fetch_add(1, Ordering::SeqCst))
  }
}

/** https://github.com/rust-lang/rfcs/blob/master/text/1210-impl-specialization.md */
pub trait ToState {
  type Target: State;

  fn to_state(&self) -> &Self::Target;
}
impl<S: State> ToState for S {
  type Target = S;

  fn to_state(&self) -> &Self::Target {
    self
  }
}
impl<S: State, T> ToState for (S, T) {
  type Target = S;

  fn to_state(&self) -> &Self::Target {
    &self.0
  }
}

use crate::boolean_algebra::BoolAlg;
/** trait for state machine */
pub trait StateMachine: Sized {
  type StateType: State;

  type BoolAlg: BoolAlg;

  /** Target of the transition */
  type Target: ToState<Target = Self::StateType> + Clone;

  type FinalState: ToState<Target = Self::StateType> + Clone;
  /*
   * https://stackoverflow.com/questions/50090578/how-to-write-a-trait-bound-for-a-reference-to-an-associated-type-on-the-trait-it
   * now, there is no way to bound the reference of an associated type.
   * bounding clone though there is no need to clone all of item.
   * i.e.
   *  wanted: filter and clone items -> collect
   *  current impl: clone -> filter -> collect
   * solutions are still open or unstable.
   */
  /** Determinizer of Output */
  type FinalSet: Clone + IntoIterator<Item = Self::FinalState> + FromIterator<Self::FinalState>;

  fn empty() -> Self;

  fn states(&self) -> &HashSet<Self::StateType>;
  fn states_mut(&mut self) -> &mut HashSet<Self::StateType>;

  fn initial_state(&self) -> &Self::StateType;
  fn initial_state_mut(&mut self) -> &mut Self::StateType;

  fn final_set(&self) -> &Self::FinalSet;
  fn final_set_mut(&mut self) -> &mut Self::FinalSet;

  fn transition(&self) -> &HashMap<(Self::StateType, Self::BoolAlg), Vec<Self::Target>>;
  fn transition_mut(&mut self)
    -> &mut HashMap<(Self::StateType, Self::BoolAlg), Vec<Self::Target>>;

  fn minimize(mut self) -> Self {
    let mut stack = vec![self.initial_state()];
    let mut reachables = vec![];
    while let Some(state) = stack.pop() {
      reachables.push(state.clone());

      for ((s, phi), target) in self.transition() {
        if s == state && phi.satisfiable() {
          for t in target {
            if !reachables.contains(t.to_state()) && !stack.contains(&t.to_state()) {
              stack.push(t.to_state());
            }
          }
        }
      }
    }

    *self.states_mut() = reachables.into_iter().collect();
    *self.transition_mut() = self
      .transition()
      .iter()
      .filter_map(|((s, phi), target)| {
        self
          .states()
          .contains(s)
          .then(|| {
            target
              .into_iter()
              .filter(|t| self.states().contains(t.to_state()))
              .cloned()
              .collect::<Vec<_>>()
          })
          .and_then(|target| {
            (target.len() != 0 && phi.satisfiable()).then(|| ((s.clone(), phi.clone()), target))
          })
      })
      .collect();
    let mut stack = vec![];
    *self.final_set_mut() = self
      .final_set()
      .clone()
      .into_iter()
      .filter(|fs| {
        if self.states().contains(fs.to_state()) {
          stack.push(fs.to_state().clone());
          true
        } else {
          false
        }
      })
      .collect();

    let mut reachables = vec![];

    while let Some(state) = stack.pop() {
      reachables.push(state.clone());

      for ((s, _), target) in self.transition() {
        for t in target {
          if *t.to_state() == state && !reachables.contains(s) && !stack.contains(s) {
            stack.push(s.clone());
          }
        }
      }
    }

    *self.states_mut() = reachables.into_iter().collect();
    *self.transition_mut() = self
      .transition()
      .iter()
      .filter_map(|((s, phi), target)| {
        self
          .states()
          .contains(s)
          .then(|| {
            target
              .into_iter()
              .filter(|t| self.states().contains(t.to_state()))
              .cloned()
              .collect::<Vec<_>>()
          })
          .and_then(|target| {
            (target.len() != 0 && phi.satisfiable()).then(|| ((s.clone(), phi.clone()), target))
          })
      })
      .collect();
    *self.final_set_mut() = self
      .final_set()
      .clone()
      .into_iter()
      .filter(|s| self.states().contains(s.to_state()))
      .collect();

    if self.states().is_empty() {
      Self::empty()
    } else {
      self
    }
  }

  fn back<Next, F>(&self, possibilities: Vec<Next>, filter_map: impl Fn(Next) -> F) -> Vec<Next>
  where
    Next: ToState<Target = Self::StateType> + Clone,
    F: FnMut(&(Self::StateType, Self::BoolAlg)) -> Option<Next>,
  {
    possibilities
      .into_iter()
      .flat_map(|curr| {
        let mut fm = filter_map(curr.clone());
        self
          .transition()
          .iter()
          .filter_map(move |(source, target)| {
            target
              .into_iter()
              .filter(|t| *t.to_state() == *curr.to_state())
              .next()
              .is_some()
              .then(|| fm(source))
              .flatten()
          })
          .collect::<Vec<_>>()
      })
      .collect()
  }

  fn step<'a, Next, F>(
    &'a self,
    possibilities: Vec<Next>,
    filter_map: impl Fn(Next) -> F,
  ) -> Vec<Next>
  where
    F: FnMut((&'a (Self::StateType, Self::BoolAlg), &'a Self::Target)) -> Option<Next>,
  {
    possibilities
      .into_iter()
      .flat_map(|curr| {
        let mut fm = filter_map(curr);
        self.transition().iter().flat_map(move |(source, target)| {
          target
            .into_iter()
            .filter_map(|t| fm((source, t)))
            .collect::<Vec<_>>()
        })
      })
      .collect()
  }

  fn generalized_run<'a, Next, F, Output>(
    &self,
    input: impl Iterator<Item = &'a <Self::BoolAlg as BoolAlg>::Domain>,
    initial_possibilities: Vec<Next>,
    step_func: &mut F,
    output_func: impl Fn(Vec<Next>) -> Output,
  ) -> Output
  where
    Next: ToState<Target = Self::StateType> + Clone,
    F: FnMut(&Next, &<Self::BoolAlg as BoolAlg>::Domain, &Self::Target) -> Next,
    <Self::BoolAlg as BoolAlg>::Domain: 'a,
  {
    let mut possibilities = initial_possibilities;

    for c in input {
      let possibilities_ = possibilities.clone();
      possibilities.clear();

      for curr in possibilities_ {
        for (source, target) in self.transition() {
          if source.0 == *curr.to_state() && source.1.denote(c) {
            for t in target {
              possibilities.push(step_func(&curr, c, t));
            }
          }
        }
      }
    }

    output_func(possibilities)
  }
}

pub(crate) mod macros {
  macro_rules! impl_state_machine {
    ( $states:ident, $initial_state:ident, $final_set:ident, $transition:ident ) => {
      fn states(&self) -> &HashSet<Self::StateType> {
        &self.$states
      }
      fn states_mut(&mut self) -> &mut HashSet<Self::StateType> {
        &mut self.$states
      }
    
      fn initial_state(&self) -> &Self::StateType {
        &self.$initial_state
      }
      fn initial_state_mut(&mut self) -> &mut Self::StateType {
        &mut self.$initial_state
      }
    
      fn final_set(&self) -> &Self::FinalSet {
        &self.$final_set
      }
      fn final_set_mut(&mut self) -> &mut Self::FinalSet {
        &mut self.$final_set
      }
    
      fn transition(&self) -> &HashMap<(Self::StateType, Self::BoolAlg), Vec<Self::Target>> {
        &self.$transition
      }
      fn transition_mut(
        &mut self,
      ) -> &mut HashMap<(Self::StateType, Self::BoolAlg), Vec<Self::Target>> {
        &mut self.$transition
      }
    };
  }

  pub(crate) use impl_state_machine;
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::collections::hash_map::{DefaultHasher, RandomState};
  use std::hash::Hasher;
  use std::iter::FromIterator;

  #[test]
  fn new_state_is_new() {
    let state_1 = StateImpl::new();
    let state_2 = StateImpl::new();

    assert_eq!(state_1, state_1);
    assert_ne!(state_1, state_2);
    assert_eq!(state_2, state_2);
    assert_ne!(state_2, state_1);
  }

  #[test]
  fn state_distingish_from_another() {
    fn new() -> StateImpl {
      State::new()
    }

    let s1 = new();
    let s2 = new();
    let s3 = s1.clone();

    assert_ne!(s1, s2);
    assert_eq!(s1, s3);

    let s1_hash = {
      let mut hasher = DefaultHasher::new();
      s1.hash(&mut hasher);
      hasher.finish()
    };
    let s2_hash = {
      let mut hasher = DefaultHasher::new();
      s2.hash(&mut hasher);
      hasher.finish()
    };
    let s3_hash = {
      let mut hasher = DefaultHasher::new();
      s3.hash(&mut hasher);
      hasher.finish()
    };

    assert_ne!(s1_hash, s2_hash);
    assert_eq!(s1_hash, s3_hash);

    let mut states100 = HashSet::with_hasher(RandomState::new());
    for _ in 0..100 {
      states100.insert(new());
    }

    let state = new();
    let states1 = vec![state; 100];
    let states1 = HashSet::<_, RandomState>::from_iter(states1.iter());

    assert_eq!(states100.len(), 100);
    assert_eq!(states1.len(), 1);
  }
}
