#![allow(dead_code)]
use super::recognizable::Recognizable;
use crate::boolean_algebra::BoolAlg;
use crate::state::State;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;

/**
 * symbolic automata
 */
#[derive(Debug)]
pub struct SymFA<T: BoolAlg + Eq + Hash> {
  pub states: HashSet<Rc<State>>,
  pub initial_state: Rc<State>,
  pub final_states: HashSet<Rc<State>>,
  pub transition: HashMap<(Rc<State>, Rc<T>), Rc<State>>,
}
impl<T: BoolAlg + Eq + Hash> SymFA<T> {
  pub fn new(
    states: HashSet<Rc<State>>,
    initial_state: Rc<State>,
    final_states: HashSet<Rc<State>>,
    transition: HashMap<(Rc<State>, Rc<T>), Rc<State>>,
  ) -> SymFA<T> {
    let mut sfa = SymFA {
      states,
      initial_state,
      final_states,
      transition,
    };
    sfa.minimize();
    sfa
  }

  fn state_predicate<'a>(&self, q: State) -> RefCell<Rc<T>> {
    let result = RefCell::new(Rc::new(T::top()));
    for (s, phi) in self.transition.keys() {
      if **s == q {
        *result.borrow_mut() = Rc::new(T::or(&Rc::clone(&result.borrow()), &Rc::clone(phi)))
      }
    }

    return result;
  }

  fn minimize(&mut self) {
    let mut stack = vec![Rc::clone(&self.initial_state)];
    let mut reachables = vec![];

    while let Some(state) = stack.pop() {
      reachables.push(Rc::clone(&state));

      for ((p, _), q) in &self.transition {
        if *p == state && !reachables.contains(&q) {
          stack.push(Rc::clone(&q));
        }
      }
    }

    self.states = reachables.into_iter().collect();
    self.transition = self
      .transition
      .iter()
      .filter_map(|((state, phi), next)| {
        if self.states.contains(state) && self.states.contains(next) {
          Some(((Rc::clone(state), Rc::clone(phi)), Rc::clone(next)))
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
impl<T: BoolAlg + Eq + Hash> Recognizable<T::Domain> for SymFA<T> {
  fn run(&self, input: &[T::Domain]) -> bool {
    let mut current_states = HashSet::new();
    current_states.insert(Rc::clone(&self.initial_state));

    for a in input {
      current_states = current_states
        .into_iter()
        .flat_map(|current_state| {
          self
            .transition
            .iter()
            .filter_map(|((state, phi), next)| {
              if *state == current_state && phi.denotate(a) {
                Some(Rc::clone(next))
              } else {
                None
              }
            })
            .collect::<HashSet<_>>()
        })
        .collect::<HashSet<_>>();
    }

    !&current_states.is_disjoint(&self.final_states)
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
  fn create_sfa_without_new() {
    let mut states = HashSet::new();
    let mut final_states = HashSet::new();
    let mut transition = HashMap::new();

    let initial_state = Rc::new(State::new());
    states.insert(Rc::clone(&initial_state));

    let rebundon_state = Rc::new(State::new());
    states.insert(Rc::clone(&rebundon_state));

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

    println!("{:#?}", sym_fa);
    assert_eq!(sym_fa.states.len(), 3);
    assert!(sym_fa.run(&"afvfdl".chars().collect::<Vec<char>>()[..]));
    assert!(!sym_fa.run(&"".chars().collect::<Vec<char>>()[..]));
    assert!(sym_fa.run(&"awa".chars().collect::<Vec<char>>()[..]));
    assert!(sym_fa.run(&"cwbwad".chars().collect::<Vec<char>>()[..]));
    assert!(!sym_fa.run(&"cwbwadww".chars().collect::<Vec<char>>()[..]));
  }

  #[test]
  fn create_sfa_with_new() {
    let mut states = HashSet::new();
    let mut final_states = HashSet::new();
    let mut transition = HashMap::new();

    let initial_state = Rc::new(State::new());
    states.insert(Rc::clone(&initial_state));

    let rebundon_state = Rc::new(State::new());
    states.insert(Rc::clone(&rebundon_state));

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

    let sym_fa = SymFA::new(states, initial_state, final_states, transition);
    println!("{:#?}", sym_fa);
    assert_eq!(sym_fa.states.len(), 2);
    assert!(sym_fa.run(&"afvfdl".chars().collect::<Vec<char>>()[..]));
    assert!(!sym_fa.run(&"".chars().collect::<Vec<char>>()[..]));
    assert!(sym_fa.run(&"awa".chars().collect::<Vec<char>>()[..]));
    assert!(sym_fa.run(&"cwbwad".chars().collect::<Vec<char>>()[..]));
    assert!(!sym_fa.run(&"cwbwadww".chars().collect::<Vec<char>>()[..]));
  }
}
