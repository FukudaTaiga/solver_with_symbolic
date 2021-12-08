use std::{
  collections::{HashMap, HashSet},
  fmt::Debug,
  hash::{Hash, Hasher},
  rc::Rc,
  cell::{RefCell},
};

static mut INTERNAL: usize = 0;
fn inc() -> usize {
  unsafe {
    INTERNAL += 1;
    INTERNAL
  }
}

#[derive(Debug, Hash, Eq)]
pub struct State(usize);
impl State {
  pub fn new() -> State {
    State(inc())
  }
}
impl Clone for State {
  fn clone(&self) -> Self {
    State(self.0)
  }
}
impl PartialEq for State {
  fn eq(&self, other: &Self) -> bool {
    //std::ptr::eq(self, other)
    self.0 == other.0
  }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MutableState(Rc<RefCell<State>>);
impl Hash for MutableState {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.0.borrow().hash(state)
  }
}

pub trait Mutable {
  type Item;

  fn update(&mut self, value: Self::Item);
}
impl Mutable for MutableState {
  type Item = State;

  fn update(&mut self, value: Self::Item) {
    loop {
      if let Ok(mut ptr) = self.0.try_borrow_mut() {
        *ptr = value;
        break;
      } else {
        println!("warning: race condition occurs.");
      }
    }
  }
}

pub trait StateImpl: Clone + PartialEq + Eq + Hash + Debug {
  fn new() -> Self;
}
impl StateImpl for State {
  fn new() -> Self {
    State::new()
  }
}
impl StateImpl for Rc<State> {
  fn new() -> Self {
    Rc::new(State::new())
  }
}
impl StateImpl for MutableState {
  fn new() -> Self {
    MutableState(Rc::new(RefCell::new(State::new())))
  }
}

/** trait for state machine */
pub trait StateMachine: Sized {
  type StateType: StateImpl;

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
    let mut stack = vec![self.initial_state().clone()];
    let mut reachables = vec![];
    while let Some(state) = stack.pop() {
      reachables.push(state.clone());

      for (s, t) in self.transition() {
        if *Self::source_to_state(s) == state
          && !reachables.contains(Self::target_to_state(t))
          && !stack.contains(Self::target_to_state(t))
          && !Self::is_unreachable(s)
        {
          stack.push(Self::target_to_state(t).clone());
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
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::collections::hash_map::RandomState;
  use std::iter::FromIterator;

  #[test]
  fn new_state_is_new() {
    let state_1 = State::new();
    let state_2 = State::new();

    assert_eq!(state_1, state_1);
    assert_ne!(state_1, state_2);
    assert_eq!(state_2, state_2);
    assert_ne!(state_2, state_1);
  }

  #[test]
  fn state_distingish_from_another() {
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
