use super::recognizable::Recognizable;
use crate::boolean_algebra::BoolAlg;
use crate::state::{StateImpl, StateMachine};
use std::{
  collections::{HashMap, HashSet},
  fmt::Debug,
  rc::Rc,
};

/** symbolic automata
 * each operation like concat, or, ... corresponds to regex's one.
 *
 */
#[derive(Debug, PartialEq, Clone)]
pub struct SymFA<B, S>
where
  B: BoolAlg,
  S: StateImpl,
{
  pub states: HashSet<S>,
  pub initial_state: S,
  pub final_states: HashSet<S>,
  pub transition: HashMap<(S, Rc<B>), S>,
}
impl<B, S> SymFA<B, S>
where
  B: BoolAlg,
  S: StateImpl,
{
  pub fn new(
    states: HashSet<S>,
    initial_state: S,
    final_states: HashSet<S>,
    transition: HashMap<(S, Rc<B>), S>,
  ) -> Self {
    SymFA {
      states,
      initial_state,
      final_states,
      transition,
    }
    .minimize()
  }

  pub fn state_predicate(&self, q: &S) -> Rc<B> {
    self
      .transition
      .iter()
      .filter_map(|((p, phi), _)| if *p == *q { Some(phi) } else { None })
      .fold(B::bot(), |phi, psi| B::or(&phi, psi))
  }

  pub fn concat(self, other: SymFA<B, S>) -> Self {
    let SymFA {
      states: s1,
      initial_state,
      final_states: f1,
      transition: t1,
    } = self;
    let SymFA {
      states: s2,
      initial_state: i2,
      final_states: f2,
      transition: t2,
    } = other;

    let states = s1.into_iter().chain(s2.into_iter()).collect::<HashSet<_>>();
    let final_states = if f2.contains(&i2) {
      f2.into_iter()
        .chain(f1.iter().map(|final_state| final_state.clone()))
        .collect()
    } else {
      f2
    };
    let transition = t1
      .into_iter()
      .chain(t2.into_iter().flat_map(|((state2, phi2), next2)| {
        if state2 == i2 {
          f1.iter()
            .map(|final_state| ((final_state.clone(), Rc::clone(&phi2)), next2.clone()))
            .chain(vec![((state2.clone(), Rc::clone(&phi2)), next2.clone())])
            .collect()
        } else {
          vec![((state2, phi2), next2)]
        }
      }))
      .collect::<HashMap<_, _>>();

    SymFA::new(states, initial_state, final_states, transition)
  }

  pub fn or(self, other: Self) -> Self {
    let SymFA {
      states: s1,
      initial_state: i1,
      final_states: f1,
      transition: t1,
    } = self;

    let SymFA {
      states: s2,
      initial_state: i2,
      final_states: f2,
      transition: t2,
    } = other;

    let initial_state = S::new();
    let states = s1
      .into_iter()
      .chain(s2.into_iter())
      .chain(vec![initial_state.clone()])
      .collect::<HashSet<_>>();
    let final_states = f1.into_iter().chain(f2.into_iter()).collect::<HashSet<_>>();
    let transition = t1
      .into_iter()
      .flat_map(|((state, phi), next)| {
        if state == i1 {
          vec![
            ((initial_state.clone(), Rc::clone(&phi)), next.clone()),
            ((state, phi), next),
          ]
        } else {
          vec![((state, phi), next)]
        }
      })
      .chain(t2.into_iter().flat_map(|((state, phi), next)| {
        if state == i2 {
          vec![
            ((initial_state.clone(), Rc::clone(&phi)), next.clone()),
            ((state, phi), next),
          ]
        } else {
          vec![((state, phi), next)]
        }
      }))
      .collect::<HashMap<_, _>>();

    SymFA::new(states, initial_state, final_states, transition)
  }

  pub fn inter(self, other: Self) -> Self {
    let error_msg = "Uncontrolled states exist. this will happen for developper's error";

    let SymFA {
      states: s1,
      initial_state: i1,
      final_states: f1,
      transition: t1,
    } = self;

    let SymFA {
      states: s2,
      initial_state: i2,
      final_states: f2,
      transition: t2,
    } = other;

    let cartesian = s1
      .iter()
      .flat_map(|p| s2.iter().map(move |q| ((p.clone(), q.clone()), S::new())))
      .collect::<HashMap<_, _>>();

    let final_states = cartesian
      .iter()
      .filter_map(|((p, q), s)| {
        if f1.contains(p) && f2.contains(q) {
          Some(s.clone())
        } else {
          None
        }
      })
      .collect::<HashSet<_>>();

    let transition = t1
      .iter()
      .flat_map(|((p1, phi1), q1)| {
        t2.iter()
          .map(|((p2, phi2), q2)| {
            let p = cartesian
              .get(&(p1.clone(), p2.clone()))
              .expect(error_msg)
              .clone();
            let q = cartesian
              .get(&(q1.clone(), q2.clone()))
              .expect(error_msg)
              .clone();

            ((p, phi1.and(phi2)), q)
          })
          .collect::<Vec<_>>()
      })
      .collect::<HashMap<_, _>>();

    let initial_state = cartesian.get(&(i1, i2)).expect(error_msg).clone();

    let states = cartesian.into_values().collect::<HashSet<_>>();

    SymFA::new(states, initial_state, final_states, transition)
  }

  pub fn not(self) -> Self {
    let states_ = self.states().clone();
    let not_predicates = states_
      .iter()
      .map(|state| (state, self.state_predicate(state).not()))
      .collect::<HashMap<_, _>>();

    let SymFA {
      mut states,
      initial_state,
      final_states,
      mut transition,
    } = self;

    let mut final_states = &states - &final_states;
    let fail_state = S::new();
    transition = transition
      .into_iter()
      .chain(states.iter().map(|state| {
        (
          (
            state.clone(),
            Rc::clone(not_predicates.get(state).unwrap_or(&B::bot())),
          ),
          fail_state.clone(),
        )
      }))
      .collect();
    states.insert(fail_state.clone());
    final_states.insert(fail_state);

    SymFA::new(states, initial_state, final_states, transition)
  }

  pub fn star(self) -> Self {
    let SymFA {
      mut states,
      initial_state: i,
      mut final_states,
      transition: t,
    } = self;

    let initial_state = S::new();

    states.insert(initial_state.clone());

    final_states.insert(initial_state.clone());

    let transition = t
      .into_iter()
      .flat_map(|((state, phi), next)| {
        if state == i {
          final_states
            .iter()
            .map(|final_state| ((final_state.clone(), Rc::clone(&phi)), next.clone()))
            .chain(vec![
              ((state, Rc::clone(&phi)), next.clone()),
              ((initial_state.clone(), Rc::clone(&phi)), next.clone()),
            ])
            .collect()
        } else {
          vec![((state, phi), next)]
        }
      })
      .collect();

    SymFA::new(states, initial_state, final_states, transition)
  }
}
impl<B, S> Recognizable<B::Domain> for SymFA<B, S>
where
  B: BoolAlg,
  S: StateImpl,
{
  fn member(&self, input: &[B::Domain]) -> bool {
    let mut current_states = HashSet::new();
    current_states.insert(self.initial_state.clone());

    for a in input {
      //eprintln!("char {:?}, states {:?}", a, current_states);
      current_states = current_states
        .into_iter()
        .flat_map(|current_state| {
          self
            .transition
            .iter()
            .filter_map(|((state, phi), next)| {
              if *state == current_state && phi.denotate(a) {
                Some(next.clone())
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
impl<B, S> StateMachine for SymFA<B, S>
where
  B: BoolAlg,
  S: StateImpl,
{
  type StateType = S;

  type Source = (S, Rc<B>);
  type Target = S;
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
    t
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

pub type Sfa<B, S> = SymFA<B, S>;

#[cfg(test)]
mod tests {
  use super::*;
  use crate::boolean_algebra::Predicate;
  use crate::state::State;

  #[test]
  fn create_sfa_and_test_minimize() {
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

    let abc = Predicate::range(Some('a'), Some('d'));
    let not_abc = Predicate::not(&abc);
    transition.insert(
      (Rc::clone(&initial_state), Rc::clone(&abc)),
      Rc::clone(&final_state),
    );
    transition.insert(
      (Rc::clone(&initial_state), Rc::clone(&not_abc)),
      Rc::clone(&initial_state),
    );

    let w = Predicate::eq('w');
    let not_w = Predicate::not(&w);
    transition.insert(
      (Rc::clone(&final_state), w.clone()),
      Rc::clone(&initial_state),
    );
    transition.insert(
      (Rc::clone(&final_state), not_w.clone()),
      Rc::clone(&final_state),
    );

    let sym_fa = SymFA::new(
      states.clone(),
      initial_state.clone(),
      final_states.clone(),
      transition.clone(),
    );
    println!("{:#?}", sym_fa);
    assert_eq!(sym_fa.states.len(), 2);
    assert!(sym_fa.member(&"afvfdl".chars().collect::<Vec<char>>()[..]));
    assert!(!sym_fa.member(&"".chars().collect::<Vec<char>>()[..]));
    assert!(sym_fa.member(&"awa".chars().collect::<Vec<char>>()[..]));
    assert!(sym_fa.member(&"cwbwad".chars().collect::<Vec<char>>()[..]));
    assert!(!sym_fa.member(&"cwbwadww".chars().collect::<Vec<char>>()[..]));

    let sym_fa = SymFA {
      states,
      initial_state,
      final_states,
      transition: transition,
    };
    println!("{:#?}", sym_fa);
    assert_eq!(sym_fa.states.len(), 3);
    assert!(sym_fa.member(&"afvfdl".chars().collect::<Vec<char>>()[..]));
    assert!(!sym_fa.member(&"".chars().collect::<Vec<char>>()[..]));
    assert!(sym_fa.member(&"awa".chars().collect::<Vec<char>>()[..]));
    assert!(sym_fa.member(&"cwbwad".chars().collect::<Vec<char>>()[..]));
    assert!(!sym_fa.member(&"cwbwadww".chars().collect::<Vec<char>>()[..]));
  }
}
