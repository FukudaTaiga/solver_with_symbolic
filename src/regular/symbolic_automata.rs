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
};

type Source<S, B> = (S, B);
type Target<S> = Vec<S>;

fn insert_with_check<K: Eq + std::hash::Hash, V>(
  multi_map: &mut HashMap<K, Vec<V>>,
  key: K,
  values: Vec<V>,
) {
  let vec = multi_map.entry(key).or_insert(vec![]);
  vec.extend(values);
}

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
  pub transition: HashMap<Source<S, B>, Target<S>>,
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
    mut transition: HashMap<Source<S, B>, Target<S>>,
  ) -> Self {
    let mut transition_ = HashMap::new();

    for ((p1, phi), target) in transition.drain() {
      for p2 in target {
        let tuple = (p1.clone(), p2);

        let phi_ = transition_.entry(tuple).or_insert(B::bot());

        *phi_ = phi_.or(&phi);
      }
    }

    for ((p1, p2), phi) in transition_ {
      let target = transition.entry((p1, phi)).or_insert(vec![]);

      target.push(p2);
    }

    SymFA {
      states,
      initial_state,
      final_states,
      transition,
    }
    .minimize()
  }

  pub fn empty() -> Self {
    let initial_state = S::new();

    Self {
      states: HashSet::from([S::clone(&initial_state)]),
      initial_state,
      final_states: HashSet::new(),
      transition: HashMap::new(),
    }
  }

  pub fn run<'a>(&self, input: impl IntoIterator<Item = &'a B::Domain>) -> bool
  where
    B::Domain: 'a,
  {
    self.generalized_run(
      input,
      vec![self.initial_state.clone()],
      &mut |_, _, next| next.clone(),
      |possibilities| {
        !&possibilities
          .into_iter()
          .collect::<HashSet<_>>()
          .is_disjoint(&self.final_states)
      },
    )
  }

  pub fn state_predicate(&self, q: &S) -> B {
    self
      .transition
      .iter()
      .filter_map(|((p, phi), _)| (*p == *q).then(|| phi))
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
          insert_with_check(
            &mut transition,
            (S::clone(&final_state), phi2.clone()),
            next2.clone(),
          );
        }
      }
      insert_with_check(&mut transition, (state2, phi2), next2);
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
        transition.insert((S::clone(&initial_state), phi.clone()), Vec::clone(&next));
      }

      transition.insert((state, phi), next);
    }

    for ((state, phi), next) in t2.into_iter() {
      if state == i2 {
        insert_with_check(
          &mut transition,
          (S::clone(&initial_state), phi.clone()),
          next.clone(),
        );
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
      .filter_map(|((p, q), s)| (f1.contains(p) && f2.contains(q)).then(|| S::clone(s)))
      .collect();

    let mut transition = HashMap::new();

    for ((p1, phi1), q1) in &t1 {
      for ((p2, phi2), q2) in &t2 {
        let p = S::clone(
          cartesian
            .get(&(S::clone(p1), S::clone(p2)))
            .expect(error_msg),
        );
        let target: Vec<_> = q1
          .into_iter()
          .flat_map(|s1| {
            q2.into_iter()
              .map(|s2| {
                S::clone(
                  cartesian
                    .get(&(S::clone(s1), S::clone(s2)))
                    .expect(error_msg),
                )
              })
              .collect::<Vec<_>>()
          })
          .collect();

        insert_with_check(&mut transition, (p, phi1.and(phi2)), target);
      }
    }

    let initial_state = cartesian.get(&(i1, i2)).expect(error_msg).clone();

    let states = cartesian.into_values().collect();

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
        (S::clone(state), not_predicates.get(state).unwrap().clone()),
        vec![S::clone(&fail_state)],
      );
    }
    transition.insert(
      (S::clone(&fail_state), B::all_char()),
      vec![S::clone(&fail_state)],
    );

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
          insert_with_check(
            &mut transition,
            (S::clone(final_state), phi.clone()),
            next.clone(),
          );
        }
        transition.insert((S::clone(&initial_state), phi.clone()), next.clone());
      }

      transition.insert((state, phi), next);
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
      let mut possibilities = vec![(S::clone(&self.initial_state), HashMap::new())];
      for oc in output {
        match oc {
          OutputComp::A(a) => {
            possibilities = self.step(possibilities, &|(curr, var_map)| {
              move |((p1, phi), p2)| {
                if *p1 == curr && phi.denote(a) {
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
      let next = S::clone(states.get(&tuple).unwrap());
      let (q, var_map) = tuple;

      let mut is_initial = true;

      /*
       * non-empty var map
       */
      if var_map.len() != 0 {
        for ((p1, var), p2) in &var_map {
          is_initial = is_initial && p1 == p2;
          for ((q1, psi), target) in sst.transition() {
            for (q2, alpha) in target {
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
                      possibilities = self.step(possibilities, &|(curr, var_phi, var_map)| {
                        move |((r1, phi), r2)| {
                          if *r1 == curr {
                            Some((
                              S::clone(r2),
                              var_phi.and(&phi.with_lambda(lambda.clone())),
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
                                (S::clone(next), phi.clone(), new_var_map)
                              })
                              .collect()
                          }
                        })
                        .collect();
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
                    let phi = psi.and(&phi);
                    if phi.satisfiable() {
                      let source = (source_state, phi);
                      let target = transition.entry(source).or_insert(vec![]);
                      target.push(S::clone(&next));
                    }
                  }
                }
              }
            }
          }
        }
      } else {
        for ((q1, phi), target) in sst.transition() {
          for (q2, _) in target {
            if q2 != q {
              continue;
            } else {
              let tuple = (q1, vec![]);
              let source_state = match states.get(&tuple) {
                Some(s) => S::clone(s),
                None => {
                  let new_state = S::new();
                  stack.push(tuple.clone());
                  states.insert(tuple, S::clone(&new_state));
                  new_state
                }
              };
              if phi.satisfiable() {
                let source = (source_state, phi.clone());
                let target = transition.entry(source).or_insert(vec![]);
                target.push(S::clone(&next));
              }
            }
          }
        }
      }

      if q == sst.initial_state() && is_initial {
        initial_states.insert(next);
      }
    }

    let mut states: HashSet<_> = states.into_values().collect();
    let initial_state = S::new();

    states.insert(S::clone(&initial_state));

    let transition_ = transition;
    let mut transition = HashMap::new();

    for ((s1, phi), target) in transition_.into_iter() {
      if initial_states.contains(&s1) {
        insert_with_check(
          &mut transition,
          (S::clone(&initial_state), phi.clone()),
          target.clone(),
        )
      }

      transition.insert((S::clone(&s1), phi), target);
    }

    if initial_states.intersection(&final_states).next().is_some() {
      final_states.insert(S::clone(&initial_state));
    }

    if initial_states.is_empty() {
      Self::empty()
    } else {
      SymFA::new(states, initial_state, final_states, transition)
    }
  }
}
impl<B, S> Recognizable<B::Domain> for SymFA<B, S>
where
  B: BoolAlg,
  S: State,
{
  fn member(&self, input: &[B::Domain]) -> bool {
    self.run(input)
  }
}
impl<B, S> StateMachine for SymFA<B, S>
where
  B: BoolAlg,
  S: State,
{
  type StateType = S;

  type BoolAlg = B;
  type Target = S;
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

pub type Sfa<T, S> = SymFA<Predicate<T>, S>;

use super::regex::Regex;
use crate::char_util::FromChar;
use crate::transducer::term::Lambda;

#[derive(Debug, PartialEq, Eq, std::hash::Hash, Clone)]
struct RegexPredicate<T: FromChar>(Regex<T>);
impl<T: FromChar> From<Predicate<T>> for RegexPredicate<T> {
  fn from(p: Predicate<T>) -> Self {
    match p {
      Predicate::Bool(b) => b.then(|| Self::top()).unwrap_or(Self::bot()),
      Predicate::Eq(a) => Self::char(a),
      Predicate::InSet(els) => els
        .into_iter()
        .fold(Self::bot(), |acc, curr| acc.or(&Self::char(curr))),
      Predicate::Range { left, right } => Self(Regex::Range(left, right)),
      Predicate::And(p1, p2) => Self::from(*p1).and(&Self::from(*p2)),
      Predicate::Or(p1, p2) => Self::from(*p1).and(&Self::from(*p2)),
      Predicate::Not(p) => Self::from(*p).not(),
      Predicate::WithLambda { .. } => unimplemented!(),
    }
  }
}
impl<T: FromChar> BoolAlg for RegexPredicate<T> {
  type Domain = T;
  type Term = Lambda<Self>;

  fn char(a: Self::Domain) -> Self {
    Self(Regex::Element(a))
  }
  fn and(self: &Self, other: &Self) -> Self {
    Self(self.0.clone().inter(other.0.clone()))
  }
  fn or(self: &Self, other: &Self) -> Self {
    Self(self.0.clone().or(other.0.clone()))
  }
  fn not(self: &Self) -> Self {
    Self(self.0.clone().not())
  }
  fn top() -> Self {
    Self(Regex::all())
  }
  fn bot() -> Self {
    Self(Regex::empty())
  }
  fn with_lambda(&self, _: Self::Term) -> Self {
    unimplemented!()
  }

  /** apply argument to self and return the result */
  fn denote(&self, _: &Self::Domain) -> bool {
    unimplemented!()
  }

  fn satisfiable(&self) -> bool {
    self.0 != Regex::empty()
  }
}
impl<T: FromChar, S: State> From<Sfa<T, S>> for SymFA<RegexPredicate<T>, S> {
  fn from(sfa: Sfa<T, S>) -> Self {
    let Sfa {
      mut states,
      initial_state: i,
      final_states,
      transition,
    } = sfa;

    let mut transition: HashMap<_, _> = transition
      .into_iter()
      .map(|((p1, phi), p2)| ((p1, RegexPredicate::from(phi)), p2))
      .collect();

    let initial_state = S::new();
    let final_state = S::new();
    for fs in final_states {
      transition.insert(
        (fs, RegexPredicate(Regex::epsilon())),
        vec![final_state.clone()],
      );
    }
    states.extend([initial_state.clone(), final_state.clone()]);
    transition.insert(
      (initial_state.clone(), RegexPredicate(Regex::epsilon())),
      vec![i],
    );

    Self::new(
      states,
      initial_state,
      HashSet::from([final_state]),
      transition,
    )
  }
}
impl<T: FromChar, S: State> SymFA<RegexPredicate<T>, S> {
  fn to_reg(self) -> Regex<T> {
    eprintln!("{}", self.states.len());

    if self.states.len() == 0 || self.states.len() == 1 {
      unreachable!()
    } else if self.states.len() == 2 {
      let Self {
        states: _,
        initial_state,
        mut final_states,
        transition,
      } = self;

      let initial_state = initial_state;
      let mut final_states = final_states.drain();
      let final_state = final_states.next().unwrap();

      assert!(initial_state != final_state && final_states.next().is_none());

      let mut prefix = Regex::Epsilon;
      let mut suffix = Regex::Epsilon;

      let mut reg = Regex::Empty;

      for ((p, phi), q) in transition {
        assert!(q.len() == 1);
        let q = q[0].clone();
        assert!(p != final_state && q != initial_state);
        let r = phi.0;

        eprintln!("{:?} -{:?}-> {:?}", p, r, q);

        if p == initial_state && q == initial_state {
          prefix = prefix.or(r);
        } else if p == initial_state && q == final_state {
          reg = reg.or(r);
        } else {
          suffix = suffix.or(r);
        }
      }

      prefix.concat(reg).concat(suffix)
    } else {
      let Self {
        mut states,
        initial_state,
        mut final_states,
        mut transition,
      } = self;

      let pre = states.len();

      let elim = states
        .iter()
        .find(|s| **s != initial_state && !final_states.contains(s))
        .unwrap()
        .clone();

      states = states.into_iter().filter(|s| *s != elim).collect();
      final_states = final_states.into_iter().filter(|s| *s != elim).collect();

      let star = transition
        .iter()
        .fold(Regex::epsilon(), |reg, ((p1, phi), target)| {
          if *p1 == elim && target.contains(&elim) {
            reg.or(phi.clone().0.star())
          } else {
            reg
          }
        });
      let from_elim: Vec<(_, _)> = transition
        .iter()
        .filter_map(|((s, phi), t)| {
          if *s == elim {
            let t: Vec<_> = t.into_iter().filter(|s| **s != elim).cloned().collect();
            (t.len() != 0).then(|| ((s.clone(), phi.clone()), t))
          } else {
            None
          }
        })
        .collect();
      let to_elim: Vec<(_, Vec<_>)> = transition
        .iter()
        .filter_map(|((s, phi), t)| {
          (*s != elim && t.contains(&elim)).then(|| {
            let t: Vec<_> = t.into_iter().filter(|s| **s != elim).cloned().collect();
            ((s.clone(), phi.clone()), t)
          })
        })
        .collect();
      transition = transition
        .into_iter()
        .filter(|((s, _), t)| *s != elim && !t.contains(&elim))
        .collect();

      eprintln!("building");

      for ((_, phi1), target1) in from_elim {
        for ((p, phi2), target2) in &to_elim {
          eprintln!("start");
          if target2.len() != 0 {
            insert_with_check(&mut transition, (p.clone(), phi2.clone()), target2.clone());
          }
          eprintln!("mid");
          insert_with_check(
            &mut transition,
            (
              p.clone(),
              RegexPredicate(phi2.0.clone().concat(star.clone()).concat(phi1.0.clone())),
            ),
            target1.clone(),
          );
          eprintln!("finish");
        }
      }

      eprintln!("end");

      let post = states.len();

      assert!(pre - post == 1);

      Self {
        states,
        initial_state,
        final_states,
        transition,
      }
      .to_reg()
    }
  }
}

pub fn dummy() {
  use crate::char_util::CharWrap;
  use crate::state::StateImpl;
  use crate::transducer::sst_factory::SstBuilder;
  use crate::transducer::term::VariableImpl;
  type Builder = SstBuilder<CharWrap, StateImpl, VariableImpl>;

  let sst = Builder::replace_all_reg(
    Regex::seq("a"),
    vec![OutputComp::A(FromChar::from_char('x'))],
  );
  let sfa = Regex::seq("x").concat(Regex::all().star()).to_sym_fa();
  eprintln!("{:?}", sfa);

  eprintln!(
    "x_: {:#?}",
    SymFA::<RegexPredicate<_>, _>::from(sfa.clone()).to_reg()
  );

  let pre_image = sfa.pre_image(sst);
  eprintln!("{:#?}", pre_image);
  // eprintln!(
  //   "a_: {:#?}",
  //   SymFA::<RegexPredicate<_>, _>::from(pre_image).to_reg()
  // );
}

#[cfg(test)]
mod tests {
  use super::super::regex::Regex;
  use super::*;
  use crate::char_util::CharWrap;
  use crate::transducer::sst_factory::SstBuilder;
  use crate::{boolean_algebra::Predicate, tests::helper::*};

  type Builder = SstBuilder<CharWrap, StateImpl, VariableImpl>;

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
    transition.insert((initial_state.clone(), abc), vec![final_state.clone()]);
    transition.insert(
      (initial_state.clone(), not_abc),
      vec![initial_state.clone()],
    );

    let w = Predicate::char('w');
    let not_w = Predicate::not(&w);
    transition.insert(
      (final_state.clone(), w.clone()),
      vec![initial_state.clone()],
    );
    transition.insert(
      (final_state.clone(), not_w.clone()),
      vec![final_state.clone()],
    );

    let sym_fa = SymFA::new(
      states.clone(),
      initial_state.clone(),
      final_states.clone(),
      transition.clone(),
    );
    println!("{:#?}", sym_fa);
    assert_eq!(sym_fa.states.len(), 2);
    assert!(sym_fa.run(&chars("afvfdl")));
    assert!(!sym_fa.run(&chars("")));
    assert!(sym_fa.run(&chars("awa")));
    assert!(sym_fa.run(&chars("cwbwad")));
    assert!(!sym_fa.run(&chars("cwbwadww")));

    let sym_fa = SymFA {
      states,
      initial_state,
      final_states,
      transition,
    };
    println!("{:#?}", sym_fa);
    assert_eq!(sym_fa.states.len(), 3);
    assert!(sym_fa.run(&chars("afvfdl")));
    assert!(!sym_fa.run(&chars("")));
    assert!(sym_fa.run(&chars("awa")));
    assert!(sym_fa.run(&chars("cwbwad")));
    assert!(!sym_fa.run(&chars("cwbwadww")));
  }

  #[test]
  fn pre_image_simple() {
    let rev = Builder::reverse();

    let abc = Regex::seq("abc").to_sym_fa();

    {
      assert!(abc.run(&chars("abc")));
      assert!(!abc.run(&chars("ab")));
      assert!(!abc.run(&chars("zxx")));
    }

    let cba = abc.pre_image(rev);

    {
      assert!(cba.run(&chars("cba")));
      assert!(!cba.run(&chars("abc")));
      assert!(!cba.run(&chars("ab")));
      assert!(!cba.run(&chars("cb")));
      assert!(!cba.run(&chars("zxx")));
    }
  }

  #[test]
  fn pre_image_constant() {
    let cnst = Builder::constant("xyz");

    let xyz = Regex::seq("xyz").to_sym_fa();

    {
      assert!(xyz.run(&chars("xyz")));
      assert!(!xyz.run(&chars("")));
      assert!(!xyz.run(&chars("aaam")));
      assert!(!xyz.run(&chars("x")));
    }

    let any = xyz.pre_image(cnst);

    {
      assert!(any.run(&chars("xyz")));
      assert!(any.run(&chars("")));
      assert!(any.run(&chars("aaam")));
      assert!(any.run(&chars("x")));
    }
  }

  #[test]
  fn pre_image_complex() {
    let a_to_x = Builder::replace_all_reg(Regex::seq("a"), to_replacer("x"));
    let x_ = Regex::seq("x")
      .concat(Regex::All.star())
      .to_sym_fa::<StateImpl>();

    eprintln!(
      "x_: {:#?}",
      SymFA::<RegexPredicate<_>, _>::from(x_.clone()).to_reg()
    );

    {
      assert!(x_.member(&chars("x")));
      assert!(x_.member(&chars("xyzfff")));
      assert!(!x_.member(&chars("a")));
      assert!(!x_.member(&chars("ayzfff")));
      assert!(!x_.member(&chars("kkk")));
    }

    let a_ = x_.pre_image(a_to_x);

    eprintln!(
      "a_: {:#?}",
      SymFA::<RegexPredicate<_>, _>::from(a_.clone()).to_reg()
    );

    {
      assert!(a_.member(&chars("x")));
      assert!(a_.member(&chars("xyzfff")));
      assert!(a_.member(&chars("a")));
      assert!(a_.member(&chars("ayzfff")));
      assert!(!a_.member(&chars("kkk")));
    }
  }
}
