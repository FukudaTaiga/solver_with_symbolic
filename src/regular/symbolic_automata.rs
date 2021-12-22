use super::recognizable::Recognizable;
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::state::{State, StateMachine};
use crate::transducer::{
  sst::SymSST,
  term::{OutputComp, UpdateComp, Variable},
};
use std::{
  collections::{HashMap, HashSet},
  fmt::Debug,
  rc::Rc,
};

/** symbolic automata
 * each operation like concat, or, ... corresponds to regex's one.
 */
#[derive(Debug, PartialEq, Clone)]
pub struct SymFA<B, S>
where
  B: BoolAlg,
  S: State,
{
  pub states: HashSet<S>,
  pub initial_state: S,
  pub final_states: HashSet<S>,
  pub transition: HashMap<(S, Rc<B>), S>,
}
impl<B, S> SymFA<B, S>
where
  B: BoolAlg,
  S: State,
{
  pub fn new(
    states: HashSet<S>,
    initial_state: S,
    final_states: HashSet<S>,
    transition: HashMap<(S, Rc<B>), S>,
  ) -> Self {
    let mut transition_: HashMap<(S, S), Rc<B>> = HashMap::new();

    for ((p1, phi), p2) in transition {
      let tuple = (p1, p2);
      if let Some(phi_) = transition_.get_mut(&tuple) {
        *phi_ = phi_.or(&phi);
      } else {
        transition_.insert(tuple, phi);
      }
    }

    let transition = transition_
      .into_iter()
      .map(|((p1, p2), phi)| ((p1, phi), p2))
      .collect();

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
      .fold(B::bot(), |phi, psi| phi.or(psi))
  }

  pub fn concat(self, other: SymFA<B, S>) -> Self {
    let SymFA {
      states: s1,
      initial_state,
      final_states: f1,
      mut transition,
    } = self;

    let SymFA {
      states: s2,
      initial_state: i2,
      final_states: f2,
      transition: t2,
    } = other;

    let states = s1.union(&s2).cloned().collect();

    for ((state2, phi2), next2) in t2.into_iter() {
      if state2 == i2 {
        for final_state in f1.iter() {
          transition.insert((S::clone(&final_state), Rc::clone(&phi2)), S::clone(&next2));
        }
      }
      transition.insert((state2, phi2), next2);
    }

    let final_states = if f2.contains(&i2) {
      f2.union(&f1).cloned().collect()
    } else {
      f2
    };

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
    let mut states: HashSet<_> = s1.union(&s2).cloned().collect();
    states.insert(S::clone(&initial_state));
    let final_states: HashSet<_> = f1.union(&f2).cloned().collect();

    let mut transition = HashMap::new();

    for ((state, phi), next) in t1.into_iter() {
      if state == i1 {
        transition.insert((S::clone(&initial_state), Rc::clone(&phi)), S::clone(&next));
      }

      transition.insert((state, phi), next);
    }

    for ((state, phi), next) in t2.into_iter() {
      if state == i2 {
        transition.insert((S::clone(&initial_state), Rc::clone(&phi)), S::clone(&next));
      }

      transition.insert((state, phi), next);
    }

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
      .into_iter()
      .flat_map(|p| {
        s2.iter()
          .map(move |q| ((S::clone(&p), S::clone(q)), S::new()))
      })
      .collect::<HashMap<_, _>>();

    let final_states = cartesian
      .iter()
      .filter_map(|((p, q), s)| {
        if f1.contains(p) && f2.contains(q) {
          Some(S::clone(s))
        } else {
          None
        }
      })
      .collect();

    let mut transition = HashMap::new();

    for ((p1, phi1), q1) in &t1 {
      for ((p2, phi2), q2) in &t2 {
        let p = S::clone(
          cartesian
            .get(&(S::clone(p1), S::clone(p2)))
            .expect(error_msg),
        );
        let q = S::clone(
          cartesian
            .get(&(S::clone(q1), S::clone(q2)))
            .expect(error_msg),
        );

        transition.insert((p, phi1.and(phi2)), q);
      }
    }

    let initial_state = cartesian.get(&(i1, i2)).expect(error_msg).clone();

    let states = cartesian.into_values().collect();

    eprintln!("before t: {:?}", transition);
    eprintln!("before i: {:?}", initial_state);
    eprintln!("before f: {:?}", final_states);

    SymFA::new(states, initial_state, final_states, transition)
  }

  pub fn not(self) -> Self {
    let not_predicates = self
      .states()
      .iter()
      .map(|state| (S::clone(state), self.state_predicate(state).not()))
      .collect::<HashMap<_, _>>();

    let SymFA {
      mut states,
      initial_state,
      final_states,
      mut transition,
    } = self;

    let mut final_states = &states - &final_states;
    let fail_state = S::new();

    for state in &states {
      transition.insert(
        (
          S::clone(state),
          Rc::clone(not_predicates.get(state).unwrap()),
        ),
        S::clone(&fail_state),
      );
    }
    transition.insert((S::clone(&fail_state), B::top()), S::clone(&fail_state));

    states.insert(S::clone(&fail_state));
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

    states.insert(S::clone(&initial_state));

    final_states.insert(S::clone(&initial_state));

    let mut transition = HashMap::new();

    for ((state, phi), next) in t.into_iter() {
      if state == i {
        for final_state in final_states.iter() {
          transition.insert((S::clone(final_state), Rc::clone(&phi)), S::clone(&next));
        }
        transition.insert((state, Rc::clone(&phi)), S::clone(&next));
        transition.insert((S::clone(&initial_state), Rc::clone(&phi)), next);
      } else {
        transition.insert((state, phi), next);
      }
    }

    SymFA::new(states, initial_state, final_states, transition)
  }

  pub fn pre_image<V: Variable>(self, sst: SymSST<B::Term, S, V>) -> Self {
    let mut states = HashMap::new();
    let mut initial_states: HashSet<S> = HashSet::new();
    let mut transition = HashMap::new();
    let mut final_states = HashSet::new();

    let mut stack = vec![];

    for (q, output) in sst.final_set() {
      let mut possibilities = vec![(S::clone(self.initial_state()), HashMap::new())];
      for oc in output {
        match oc {
          OutputComp::A(a) => {
            possibilities = self.step(possibilities, |(curr, var_map)| {
              move |((p1, phi), p2)| {
                if *p1 == curr && phi.denotate(a) {
                  Some((S::clone(p2), var_map.clone()))
                } else {
                  None
                }
              }
            });
          }
          OutputComp::X(x) => {
            possibilities = possibilities
              .into_iter()
              .flat_map(|(curr, var_map)| {
                if let Some(next) = var_map.get(&(S::clone(&curr), V::clone(x))) {
                  vec![(S::clone(next), var_map)]
                } else {
                  self
                    .states
                    .iter()
                    .map(|next| {
                      let mut var_map = var_map.clone();
                      var_map.insert((S::clone(&curr), V::clone(&x)), S::clone(next));
                      (S::clone(next), var_map)
                    })
                    .collect()
                }
              })
              .collect()
          }
        }
      }

      for (p, var_map) in possibilities {
        if self.final_states.contains(&p) {
          let tuple = (q, var_map.into_iter().collect::<Vec<_>>());
          stack.push(tuple.clone());
          states.entry(tuple).or_insert({
            let new_state = S::new();
            final_states.insert(S::clone(&new_state));
            new_state
          });
        }
      }
    }

    while let Some(tuple) = stack.pop() {
      let target = S::clone(states.get(&tuple).unwrap());
      let (q, var_map) = tuple;

      let mut is_initial = true;

      for ((p1, var), p2) in &var_map {
        is_initial = is_initial && p1 == p2;

        for ((q1, psi), (q2, alpha)) in sst.transition() {
          if q2 != q {
            continue;
          } else {
            let mut possibilities = vec![(S::clone(p1), B::top(), HashMap::new())];

            for uc in alpha
              .get(var)
              .unwrap_or(&vec![UpdateComp::X(V::clone(var))])
              .into_iter()
            {
              match uc {
                UpdateComp::F(lambda) => {
                  possibilities = self.step(possibilities, |(curr, var_phi, var_map)| {
                    move |((r1, phi), r2)| {
                      if *r1 == curr {
                        Some((
                          S::clone(r2),
                          var_phi.and(&Rc::clone(phi).with_lambda(lambda.clone())),
                          var_map.clone(),
                        ))
                      } else {
                        None
                      }
                    }
                  });
                }
                UpdateComp::X(x) => {
                  possibilities = possibilities
                    .into_iter()
                    .flat_map(|(r, phi, var_map)| {
                      if let Some(next) = var_map.get(&(S::clone(&r), V::clone(x))) {
                        vec![(S::clone(next), phi, var_map)]
                      } else {
                        self
                          .states
                          .iter()
                          .map(|next| {
                            let mut new_var_map = var_map.clone();
                            new_var_map.insert((S::clone(&r), V::clone(&x)), S::clone(next));
                            (S::clone(next), Rc::clone(&phi), new_var_map)
                          })
                          .collect()
                      }
                    })
                    .collect()
                }
              }
            }

            for (p, phi, var_map) in possibilities {
              if p == *p2 {
                let tuple = (q1, var_map.into_iter().collect());
                let source_state = match states.get(&tuple) {
                  Some(s) => S::clone(s),
                  None => {
                    let new_state = S::new();
                    stack.push(tuple.clone());
                    states.insert(tuple, S::clone(&new_state));
                    new_state
                  }
                };
                let source = (source_state, psi.and(&phi));
                transition.insert(source, S::clone(&target));
              }
            }
          }
        }
      }

      if is_initial {
        initial_states.insert(target);
      }
    }

    let mut states: HashSet<_> = states.into_values().collect();
    let initial_state = S::new();

    states.insert(S::clone(&initial_state));

    let transition_ = transition;
    let mut transition = HashMap::new();

    for ((s1, phi), s2) in transition_.into_iter() {
      if initial_states.contains(&s1) {
        transition.insert((S::clone(&initial_state), Rc::clone(&phi)), S::clone(&s2));
      }

      transition.insert((S::clone(&s1), Rc::clone(&phi)), S::clone(&s2));
    }

    SymFA::new(states, initial_state, final_states, transition)
  }
}
impl<B, S> Recognizable<B::Domain> for SymFA<B, S>
where
  B: BoolAlg,
  S: State,
{
  fn member(&self, input: &[B::Domain]) -> bool {
    let mut possibilities = vec![self.initial_state.clone()];

    for c in input {
      //eprintln!("char {:?}, states {:?}", a, current_states);
      possibilities = self.step(possibilities, |current_state| {
        move |((state, phi), next)| {
          if *state == current_state && phi.denotate(c) {
            Some(next.clone())
          } else {
            None
          }
        }
      });
    }

    !&possibilities
      .into_iter()
      .collect::<HashSet<_>>()
      .is_disjoint(&self.final_states)
  }
}
impl<B, S> StateMachine for SymFA<B, S>
where
  B: BoolAlg,
  S: State,
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

pub type Sfa<T, S> = SymFA<Predicate<T>, S>;

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{boolean_algebra::Predicate, tests::helper::*};

  #[test]
  fn create_sfa_and_test_minimize() {
    let mut states = HashSet::new();
    let mut final_states = HashSet::new();
    let mut transition = HashMap::new();

    let initial_state = StateImpl::new();
    states.insert(initial_state.clone());

    let rebundon_state = StateImpl::new();
    states.insert(rebundon_state.clone());

    let final_state = StateImpl::new();
    states.insert(final_state.clone());
    final_states.insert(final_state.clone());

    let abc = Predicate::range(Some('a'), Some('d'));
    let not_abc = Predicate::not(&abc);
    transition.insert(
      (initial_state.clone(), Rc::clone(&abc)),
      final_state.clone(),
    );
    transition.insert(
      (initial_state.clone(), Rc::clone(&not_abc)),
      initial_state.clone(),
    );

    let w = Predicate::eq('w');
    let not_w = Predicate::not(&w);
    transition.insert((final_state.clone(), w.clone()), initial_state.clone());
    transition.insert((final_state.clone(), not_w.clone()), final_state.clone());

    let sym_fa = SymFA::new(
      states.clone(),
      initial_state.clone(),
      final_states.clone(),
      transition.clone(),
    );
    println!("{:#?}", sym_fa);
    assert_eq!(sym_fa.states.len(), 2);
    assert!(sym_fa.member(&chars("afvfdl")));
    assert!(!sym_fa.member(&chars("")));
    assert!(sym_fa.member(&chars("awa")));
    assert!(sym_fa.member(&chars("cwbwad")));
    assert!(!sym_fa.member(&chars("cwbwadww")));

    let sym_fa = SymFA {
      states,
      initial_state,
      final_states,
      transition,
    };
    println!("{:#?}", sym_fa);
    assert_eq!(sym_fa.states.len(), 3);
    assert!(sym_fa.member(&chars("afvfdl")));
    assert!(!sym_fa.member(&chars("")));
    assert!(sym_fa.member(&chars("awa")));
    assert!(sym_fa.member(&chars("cwbwad")));
    assert!(!sym_fa.member(&chars("cwbwadww")));
  }
}
