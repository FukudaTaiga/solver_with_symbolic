use std::{
  collections::{HashMap, HashSet},
  fmt::Debug,
  hash::Hash,
  sync::atomic::{AtomicUsize, Ordering},
  rc::Rc,
};

static STATE_CNT: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, PartialEq, Hash, Eq, Clone)]
pub struct StateImpl(usize);
impl StateImpl {
  pub fn new() -> StateImpl {
    StateImpl(STATE_CNT.fetch_add(1, Ordering::SeqCst))
  }
}

pub trait State: Clone + PartialEq + Eq + Hash + Debug {
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

/** trait for state machine */
pub trait StateMachine: Sized {
  type StateType: State;

  /** Source of the transition */
  type Source: Eq + Hash + Clone;
  /** Target of the transition */
  type Target: Clone;
  /** Determinizer of Output */
  type FinalSet;

  fn states(&self) -> &HashSet<Self::StateType>;
  fn states_mut(&mut self) -> &mut HashSet<Self::StateType>;

  fn initial_state(&self) -> &Self::StateType;
  fn initial_state_mut(&mut self) -> &mut Self::StateType;

  fn final_set(&self) -> &Self::FinalSet;
  fn final_set_mut(&mut self) -> &mut Self::FinalSet;
  fn final_set_filter_by_states<T: FnMut(&Self::StateType) -> bool>(
    &self,
    filter: T,
  ) -> Self::FinalSet;

  fn source_to_state(s: &Self::Source) -> &Self::StateType;
  fn target_to_state(t: &Self::Target) -> &Self::StateType;

  fn transition(&self) -> &HashMap<Self::Source, Self::Target>;
  fn transition_mut(&mut self) -> &mut HashMap<Self::Source, Self::Target>;
  fn is_unreachable(s: &Self::Source) -> bool;

  fn minimize(mut self) -> Self {
    let mut stack = vec![self.initial_state()];
    let mut reachables = vec![];
    while let Some(state) = stack.pop() {
      reachables.push(state.clone());

      for (s, t) in self.transition() {
        if Self::source_to_state(s) == state
          && !reachables.contains(Self::target_to_state(t))
          && !stack.contains(&Self::target_to_state(t))
          && !Self::is_unreachable(s)
        {
          stack.push(Self::target_to_state(t));
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
          Some((s.clone(), t.clone()))
        } else {
          None
        }
      })
      .collect();
    let mut stack = vec![];
    *self.final_set_mut() = self.final_set_filter_by_states(|s| {
      if self.states().contains(s) {
        stack.push(s.clone());
        true
      } else {
        false
      }
    });

    let mut reachables = vec![];

    while let Some(state) = stack.pop() {
      reachables.push(state.clone());

      for (s, t) in self.transition() {
        if *Self::target_to_state(t) == state
          && !reachables.contains(Self::source_to_state(s))
          && !stack.contains(Self::source_to_state(s))
          && !Self::is_unreachable(s)
        {
          stack.push(Self::source_to_state(s).clone());
        }
      }
    }

    /*
     * this code may not be necessary,
     * but some method will panic if no state exists like sfa.inter()
     * hopefully such function would check if the operation can be done.
     */
    reachables.push(self.initial_state().clone());

    *self.states_mut() = reachables.into_iter().collect();
    *self.transition_mut() = self
      .transition()
      .iter()
      .filter_map(|(s, t)| {
        if self.states().contains(Self::source_to_state(s))
          && self.states().contains(Self::target_to_state(t))
        {
          Some((s.clone(), t.clone()))
        } else {
          None
        }
      })
      .collect();
    *self.final_set_mut() = self.final_set_filter_by_states(|s| self.states().contains(s));

    self
  }

  fn step<Next, F: FnMut((&Self::Source, &Self::Target)) -> Option<Next>>(
    &self,
    possibilities: Vec<Next>,
    filter_map: impl Fn(Next) -> F,
  ) -> Vec<Next> {
    possibilities
      .into_iter()
      .flat_map(|curr| self.transition().iter().filter_map(filter_map(curr)))
      .collect()
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;
  use std::collections::hash_map::{RandomState, DefaultHasher};
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
    fn new() -> Rc<StateImpl> {
      State::new()
    }
    
    let s1 = new();
    let s2 = new();
    let s3 = s1.clone();

    assert_ne!(s1, s2);
    assert!(s1 == s3 && s1.0 == s3.0);

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
