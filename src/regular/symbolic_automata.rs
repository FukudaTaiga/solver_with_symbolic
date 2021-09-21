#![allow(dead_code)]
use super::recognizable::Recognizable;
use crate::boolean_algebra::BoolAlg;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

static mut INTERNAL: u64 = 0;

#[derive(Debug, Hash, Eq, Clone)]
pub struct State {
  value: u64,
}
impl State {
  pub fn new() -> State {
    unsafe {
      INTERNAL += 1;
      State { value: INTERNAL }
    }
  }
}
impl PartialEq for State {
  fn eq(&self, other: &Self) -> bool {
    //std::ptr::eq(self, other)
    self.value == other.value
  }
}

/**
 * symbolic automata
 */
#[derive(Debug)]
pub struct SymFA<T: BoolAlg> {
  pub states: HashSet<Rc<State>>,
  pub initial_state: Rc<State>,
  pub final_states: HashSet<Rc<State>>,
  pub transition: HashMap<(Rc<State>, Rc<T>), Rc<State>>,
}
impl<T: BoolAlg> SymFA<T> {
  fn state_predicate<'a>(&self, q: State) -> RefCell<Rc<T>> {
    let result = RefCell::new(Rc::new(T::top()));
    for (s, phi) in self.transition.keys() {
      if **s == q {
        *result.borrow_mut() = Rc::new(T::or(&Rc::clone(&result.borrow()), &Rc::clone(phi)))
      }
    }

    return result;
  }
}
impl<T: BoolAlg> Recognizable<T::Domain> for SymFA<T> {
  fn run(&self, input: &[T::Domain]) -> bool {
    let mut current_state = &self.initial_state;

    for a in input {
      let mut available_states = self.transition.iter().filter_map(|((state, phi), next)| {
        if *state == *current_state && phi.denotate(a) {
          Some(next)
        } else {
          None
        }
      });

      current_state = match available_states.next() {
        Some(s) => s,
        None => return false,
      }
    }

    self.final_states.contains(current_state)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::boolean_algebra::Predicate;
  use std::collections::hash_map::RandomState;
  use std::iter::FromIterator;

  #[test]
  fn new_state_test() {
    let state_1 = State::new();
    let state_2 = State::new();

    assert_eq!(state_1, state_1);
    assert_ne!(state_1, state_2);
    assert_eq!(state_2, state_2);
    assert_ne!(state_2, state_1);
  }

  #[test]
  fn state_set_test() {
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

  #[test]
  fn create_sym_fa() {
    let mut states = HashSet::new();
    let mut final_states = HashSet::new();
    let mut transition = HashMap::new();

    let initial_state = Rc::new(State::new());
    states.insert(Rc::clone(&initial_state));

    let final_state = Rc::new(State::new());
    states.insert(Rc::clone(&final_state));
    final_states.insert(Rc::clone(&final_state));

    let abc = Rc::new(Predicate::range(Some('a'), Some('d')).unwrap());
    let not_abc = Rc::new(Predicate::not(&abc));
    transition.insert(
      (Rc::clone(&initial_state), Rc::clone(&abc)),
      Rc::clone(&final_state),
    );
    transition.insert(
      (Rc::clone(&initial_state), Rc::clone(&not_abc)),
      Rc::clone(&initial_state),
    );

    let w = Rc::new(Predicate::eq('w'));
    let not_w = Rc::new(Predicate::not(&w));
    transition.insert(
      (Rc::clone(&final_state), Rc::clone(&w)),
      Rc::clone(&initial_state),
    );
    transition.insert(
      (Rc::clone(&final_state), Rc::clone(&not_w)),
      Rc::clone(&final_state),
    );

    let sym_fa = SymFA {
      states,
      initial_state,
      final_states,
      transition,
    };

    eprintln!("{:#?}", sym_fa);
    assert!(sym_fa.run(&"afvfdl".chars().collect::<Vec<char>>()[..]));
    assert!(!sym_fa.run(&"".chars().collect::<Vec<char>>()[..]));
    assert!(sym_fa.run(&"awa".chars().collect::<Vec<char>>()[..]));
    assert!(sym_fa.run(&"cwbwad".chars().collect::<Vec<char>>()[..]));
    assert!(!sym_fa.run(&"cwbwadww".chars().collect::<Vec<char>>()[..]));
  }
}
