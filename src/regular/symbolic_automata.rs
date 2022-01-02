use super::recognizable::Recognizable;
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::state::{self, State, StateMachine};
use crate::transducer::{
  sst::SymSST,
  term::{OutputComp, UpdateComp, Variable},
};
use crate::util::{extention::MultiMap, Domain};
use std::{
  collections::{HashMap, HashSet},
  fmt::Debug,
};

type Source<S, B> = (S, B);
type Target<S> = Vec<S>;

/** symbolic automata
 * each operation like concat, or, ... corresponds to regex's one.
 */
#[derive(Debug, PartialEq, Clone)]
pub struct SymFA<D, B, S>
where
  D: Domain,
  B: BoolAlg<Domain = D>,
  S: State,
{
  pub states: HashSet<S>,
  pub initial_state: S,
  pub final_states: HashSet<S>,
  pub transition: HashMap<Source<S, B>, Target<S>>,
}
impl<D, B, S> SymFA<D, B, S>
where
  D: Domain,
  B: BoolAlg<Domain = D>,
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

  pub fn run<'a>(&self, input: impl IntoIterator<Item = &'a B::Domain>) -> bool
  where
    B::Domain: 'a,
  {
    self.generalized_run(
      input.into_iter(),
      vec![self.initial_state.clone()],
      &mut |_, _, next| S::clone(next),
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

  pub fn concat(self, other: Self) -> Self {
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
          transition.insert_with_check((S::clone(&final_state), phi2.clone()), next2.clone());
        }
      }
      transition.insert_with_check((state2, phi2), next2);
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

    for ((state, phi), target) in t2.into_iter() {
      if state == i2 {
        transition.insert_with_check((S::clone(&initial_state), phi.clone()), target.clone());
      }

      transition.insert((state, phi), target);
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

        transition.insert_with_check((p, phi1.and(phi2)), target);
      }
    }

    let initial_state = cartesian.get(&(i1, i2)).expect(error_msg).clone();

    let states = cartesian.into_values().collect();

    SymFA::new(states, initial_state, final_states, transition)
  }

  pub fn not(self) -> Self {
    let not_predicates = self
      .states
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
    let dead_state = S::new();

    for state in &states {
      transition.insert(
        (S::clone(state), not_predicates.get(state).unwrap().clone()),
        vec![S::clone(&dead_state)],
      );
    }
    transition.insert(
      (S::clone(&dead_state), B::all_char()),
      vec![S::clone(&dead_state)],
    );

    states.insert(S::clone(&dead_state));
    final_states.insert(dead_state);

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

    for ((state, phi), target) in t.into_iter() {
      if state == i {
        for final_state in final_states.iter() {
          transition.insert_with_check((S::clone(final_state), phi.clone()), target.clone());
        }
        transition.insert((S::clone(&initial_state), phi.clone()), target.clone());
      }

      transition.insert((state, phi), target);
    }

    SymFA::new(states, initial_state, final_states, transition)
  }

  pub fn pre_image<V: Variable>(self, sst: SymSST<D, B, <B as BoolAlg>::Term, S, V>) -> Self {
    eprintln!("{:?}\n", sst);
    let mut states = HashMap::new();
    let mut initial_states = HashSet::new();
    let mut transition: HashMap<_, Vec<_>> = HashMap::new();
    let mut final_states = HashSet::new();

    let mut stack = vec![];

    macro_rules! step_with_var {
      ( $possibilities:ident,
        $var_name:ident,
        | $curr:ident, $var_map:ident, $($others:ident),* |
      ) => {
        $possibilities
          .into_iter()
          .flat_map(|($curr, $var_map, $($others),*)| {
            self.states.iter().map(move |next| {
              let mut $var_map = $var_map.clone();
              let target = $var_map.entry(($curr, $var_name)).or_insert(vec![]);
              if target.contains(&next) {
                (next, $var_map, $($others.clone()),*)
              } else {
                target.push(next);
                (next, $var_map, $($others.clone()),*)
              }
            })
          })
          .collect()
      };
    }

    for (q, output) in sst.final_set() {
      let mut possibilities = vec![(&self.initial_state, HashMap::new())];
      for oc in output {
        match oc {
          OutputComp::A(a) => {
            possibilities = self.step(possibilities, |(curr, var_map)| {
              move |((p1, phi), p2)| (*p1 == *curr && phi.denote(a)).then(|| (p2, var_map.clone()))
            });
          }
          OutputComp::X(x) => {
            possibilities = step_with_var!(possibilities, x, |curr, var_map,|);
          }
        }
      }

      for (p, var_map) in possibilities {
        if self.final_states.contains(p) {
          let mut var_map: Vec<_> = var_map.into_iter().collect();
          var_map.sort();
          let tuple = (q, var_map);
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

      for ((q1, psi), target) in sst.transition() {
        'add_update: for (_, alpha) in target.into_iter().filter(|(s, _)| *s == *q) {
          let mut phi = HashMap::new();
          let mut pre_maps: HashMap<_, Vec<_>> = HashMap::new();

          for ((p1, var), nexts) in &var_map {
            let mut possibilities = vec![(*p1, HashMap::new(), B::top())];
            if let Some(seq) = alpha.get(*var) {
              for uc in seq.into_iter() {
                match uc {
                  UpdateComp::F(lambda) => {
                    possibilities = self.step(possibilities, |(curr, var_map, var_phi)| {
                      move |((r1, phi), r2)| {
                        (*r1 == *curr)
                          .then(|| var_phi.and(&phi.with_lambda(lambda)))
                          .and_then(|var_phi| {
                            var_phi
                              .satisfiable()
                              .then(|| (r2, var_map.clone(), var_phi))
                          })
                      }
                    });
                  }
                  UpdateComp::X(x) => {
                    possibilities = step_with_var!(possibilities, x, |curr, var_map, var_phi|);
                  }
                }
              }
            } else {
              /*
               * if update function has no corresponding output, update with identity function
               * i.e. update(var) = vec![UpdateComp::X(var)]
               */
              possibilities = step_with_var!(possibilities, var, |curr, var_map, var_phi|);
            }

            /*
             * if both sst and sfa are minimized, nexts.len() != 0. it cannot panic
             * if nexts.len() over 64, then it will not working => check possibilities consists of all of nexts with iterator.
             */
            let mut is_nexts_covered: usize = (1 << nexts.len()) - 1;
            possibilities = possibilities
              .into_iter()
              .filter(|(p, _, _)| {
                if let Some(pos) = nexts.iter().position(|s| **s == **p) {
                  is_nexts_covered = is_nexts_covered & (!(1 << pos));
                  true
                } else {
                  false
                }
              })
              .collect();

            if is_nexts_covered == 0 {
              for (p, var_map, var_phi) in possibilities {
                let p_phi = phi.entry((*p1, *var, p)).or_insert(B::bot());
                *p_phi = p_phi.or(&var_phi);
                pre_maps.insert_with_check(*var, [var_map]);
              }
            } else {
              continue 'add_update;
            }
          }
          eprintln!();

          let phi = phi
            .into_values()
            .reduce(|phi, p_phi| phi.and(&p_phi))
            .unwrap_or(B::boolean(var_map.is_empty()))
            .and(psi);

          if phi.satisfiable() {
            /* calculate each combination of pre_maps */
            let pre_maps = {
              let mut combination = vec![HashMap::new()];

              for pre_maps in pre_maps.into_values() {
                combination = combination
                  .into_iter()
                  .flat_map(move |map| {
                    let mut pre_maps = pre_maps.clone();
                    pre_maps.iter_mut().for_each(|pre_map| {
                      pre_map.merge(map.clone());
                    });

                    pre_maps
                  })
                  .collect();
              }

              combination
            };

            for pre_map in pre_maps {
              let tuple = (q1, pre_map.into_iter().collect());
              let source_state = match states.get(&tuple) {
                Some(s) => S::clone(s),
                None => {
                  let new_state = S::new();
                  if !stack.contains(&tuple) {
                    stack.push(tuple.clone());
                  }
                  states.insert(tuple, S::clone(&new_state));
                  new_state
                }
              };

              let source = (source_state, phi.clone());
              transition.insert_with_check(source, [S::clone(&next)]);
            }
          }
        }
      }

      let is_initial = var_map
        .iter()
        .all(|((p1, _), nexts)| nexts.len() == 1 && nexts.contains(p1));

      if *q == *sst.initial_state() && is_initial {
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
        transition.insert_with_check((S::clone(&initial_state), phi.clone()), target.clone());
      }

      transition.insert((s1, phi), target);
    }

    if initial_states.intersection(&final_states).next().is_some() {
      final_states.insert(S::clone(&initial_state));
    }

    if initial_states.is_empty() {
      SymFA::empty()
    } else {
      SymFA::new(states, initial_state, final_states, transition)
    }
  }
}
impl<D, B, S> Recognizable<D> for SymFA<D, B, S>
where
  D: Domain,
  B: BoolAlg<Domain = D>,
  S: State,
{
  fn member(&self, input: &[B::Domain]) -> bool {
    self.run(input)
  }
}
impl<D, B, S> StateMachine for SymFA<D, B, S>
where
  D: Domain,
  B: BoolAlg<Domain = D>,
  S: State,
{
  type StateType = S;
  type BoolAlg = B;
  type Target = S;
  type FinalState = S;
  type FinalSet = HashSet<S>;

  fn empty() -> Self {
    let initial_state = S::new();

    Self {
      states: HashSet::from([S::clone(&initial_state)]),
      initial_state,
      final_states: HashSet::new(),
      transition: HashMap::new(),
    }
  }

  state::macros::impl_state_machine!(states, initial_state, final_states, transition);
}

pub type Sfa<T, S> = SymFA<T, Predicate<T>, S>;

#[cfg(test)]
mod tests {
  use super::super::regex::Regex;
  use super::*;
  use crate::transducer::sst_factory::SstBuilder;
  use crate::util::CharWrap;
  use crate::{boolean_algebra::Predicate, tests::helper::*};

  type Builder = SstBuilder<CharWrap, StateImpl, VariableImpl>;

  mod helper {
    use super::*;
    use crate::transducer::term::Lambda;

    #[derive(Debug, PartialEq, Eq, std::hash::Hash, Clone)]
    pub struct RegexPredicate<T: Domain>(Regex<T>);
    impl<T: Domain> From<Predicate<T>> for RegexPredicate<T> {
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
    impl<T: Domain> BoolAlg for RegexPredicate<T> {
      type Domain = T;
      type Term = Lambda<Self>;

      fn char(a: Self::Domain) -> Self {
        Self(Regex::Element(a))
      }
      fn and(&self, other: &Self) -> Self {
        Self(self.0.clone().inter(other.0.clone()))
      }
      fn or(&self, other: &Self) -> Self {
        Self(self.0.clone().or(other.0.clone()))
      }
      fn not(&self) -> Self {
        Self(self.0.clone().not())
      }
      fn top() -> Self {
        Self(Regex::all())
      }
      fn bot() -> Self {
        Self(Regex::empty())
      }
      fn with_lambda(&self, _: &Self::Term) -> Self {
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
    impl<T: Domain, S: State> From<Sfa<T, S>> for SymFA<T, RegexPredicate<T>, S> {
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
          transition.insert_with_check(
            (fs, RegexPredicate(Regex::epsilon())),
            [final_state.clone()],
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
    impl<T: Domain, S: State> SymFA<T, RegexPredicate<T>, S> {
      pub fn to_reg(self) -> Regex<T> {
        if self.states.len() == 0 {
          unreachable!()
        } else if self.states.len() == 1 {
          Regex::empty()
        } else if self.states.len() == 2 {
          let Self {
            states: _,
            initial_state,
            mut final_states,
            transition,
          } = self.minimize();

          let initial_state = initial_state;
          let mut final_states = final_states.drain();
          let final_state = final_states.next().unwrap();

          assert!(initial_state != final_state && final_states.next().is_none());

          let mut prefix = Regex::Epsilon;
          let mut suffix = Regex::Epsilon;

          let mut reg = Regex::Empty;

          for ((p, phi), q) in transition {
            assert!(p != final_state || q.len() == 1);
            assert!(!q.contains(&initial_state));

            for q in q {
              let r = phi.0.clone();
              eprintln!("{:?} -{:?}-> {:?}", p, r, q);

              if p == initial_state && q == initial_state {
                prefix = prefix.or(r);
              } else if p == initial_state && q == final_state {
                reg = reg.or(r);
              } else if p == final_state && q == final_state {
                suffix = suffix.or(r);
              } else {
                unreachable!()
              }
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
              (*s == elim)
                .then(|| {
                  t.into_iter()
                    .filter(|s| **s != elim)
                    .cloned()
                    .collect::<Vec<_>>()
                })
                .and_then(|t| (t.len() != 0).then(|| ((s.clone(), phi.clone()), t)))
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

          for ((_, phi1), target1) in from_elim {
            for ((p, phi2), target2) in &to_elim {
              if target2.len() != 0 {
                transition.insert_with_check((p.clone(), phi2.clone()), target2.clone());
              }
              transition.insert_with_check(
                (
                  p.clone(),
                  RegexPredicate(phi2.0.clone().concat(star.clone()).concat(phi1.0.clone())),
                ),
                target1.clone(),
              );
            }
          }

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
  }

  #[test]
  fn create_sfa_and_minimize() {
    let mut transition = HashMap::new();

    let initial_state = StateImpl::new();

    let dead_state = StateImpl::new();

    let final_state = StateImpl::new();

    let states = HashSet::from([
      initial_state.clone(),
      dead_state.clone(),
      final_state.clone(),
    ]);
    let final_states = HashSet::from([final_state.clone()]);

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
  fn pre_image_identity() {
    let id = Builder::identity();

    let reg = Regex::seq("xyz")
      .or(Regex::range(Some('o'), Some('r')).star())
      .to_sym_fa();

    assert!(reg.run(&chars("xyz")));
    assert!(!reg.run(&chars("xyz__")));
    assert!(!reg.run(&chars("")));
    assert!(!reg.run(&chars("aaam")));
    assert!(!reg.run(&chars("x")));
    assert!(reg.run(&chars("ooqppq")));

    let pre_image = reg.pre_image(id);

    assert!(pre_image.run(&chars("xyz")));
    assert!(!pre_image.run(&chars("xyz__")));
    assert!(!pre_image.run(&chars("")));
    assert!(!pre_image.run(&chars("aaam")));
    assert!(!pre_image.run(&chars("x")));
    assert!(pre_image.run(&chars("ooqppq")));
  }

  #[test]
  fn pre_image_rev() {
    let rev = Builder::reverse();

    let abc = Regex::seq("abc").to_sym_fa();

    assert!(abc.run(&chars("abc")));
    assert!(!abc.run(&chars("ab")));
    assert!(!abc.run(&chars("kkk")));

    let cba = abc.pre_image(rev.clone());

    assert!(cba.run(&chars("cba")));
    assert!(!cba.run(&chars("abc")));
    assert!(!cba.run(&chars("ab")));
    assert!(!cba.run(&chars("cb")));
    assert!(!cba.run(&chars("kkk")));

    let abc_xystar = Regex::seq("abc")
      .concat(Regex::element('x').or(Regex::element('y')).star())
      .to_sym_fa();

    assert!(abc_xystar.run(&chars("abc")));
    assert!(!abc_xystar.run(&chars("ab")));
    assert!(!abc_xystar.run(&chars("kkk")));
    assert!(abc_xystar.run(&chars("abcxx")));
    assert!(abc_xystar.run(&chars("abcxyxyxyy")));
    assert!(abc_xystar.run(&chars("abcyy")));
    assert!(!abc_xystar.run(&chars("xxx")));
    assert!(!abc_xystar.run(&chars("yy")));

    let xystar_cba = abc_xystar.pre_image(rev);

    assert!(xystar_cba.run(&chars("cba")));
    assert!(!xystar_cba.run(&chars("abc")));
    assert!(!xystar_cba.run(&chars("ab")));
    assert!(!xystar_cba.run(&chars("cb")));
    assert!(!xystar_cba.run(&chars("kkk")));
    assert!(xystar_cba.run(&chars("xxcba")));
    assert!(xystar_cba.run(&chars("yyxyxyxcba")));
    assert!(xystar_cba.run(&chars("yycba")));
    assert!(!xystar_cba.run(&chars("xxx")));
    assert!(!xystar_cba.run(&chars("yy")));
  }

  #[test]
  fn pre_image_constant() {
    let cnst = Builder::constant("xyz");

    let xyz = Regex::seq("xyz").to_sym_fa();

    assert!(xyz.run(&chars("xyz")));
    assert!(!xyz.run(&chars("xyz__")));
    assert!(!xyz.run(&chars("")));
    assert!(!xyz.run(&chars("aaam")));
    assert!(!xyz.run(&chars("x")));

    let any = xyz.pre_image(cnst);

    assert!(any.run(&chars("xyz")));
    assert!(any.run(&chars("xyz__")));
    assert!(any.run(&chars("")));
    assert!(any.run(&chars("aaam")));
    assert!(any.run(&chars("x")));
  }

  #[test]
  fn pre_image_replace_one_all() {
    let a_to_x = Builder::replace_all_reg(Regex::seq("a"), to_replacer("x"));

    let x = Regex::seq("x").to_sym_fa::<StateImpl>();

    assert!(x.member(&chars("x")));
    assert!(!x.member(&chars("xyzfff")));
    assert!(!x.member(&chars("a")));
    assert!(!x.member(&chars("ayzfff")));
    assert!(!x.member(&chars("kkk")));

    let a = x.pre_image(a_to_x);

    assert!(a.member(&chars("x")));
    assert!(!a.member(&chars("xyzfff")));
    assert!(a.member(&chars("a")));
    assert!(!a.member(&chars("ayzfff")));
    assert!(!a.member(&chars("kkk")));
  }

  #[test]
  fn pre_image_replace_concat_all() {
    let abc_to_xyz = Builder::replace_all_reg(Regex::seq("abc"), to_replacer("xyz"));

    let xyz = Regex::seq("xyz").to_sym_fa::<StateImpl>();

    assert!(xyz.member(&chars("xyz")));
    assert!(!xyz.member(&chars("xyzzfff")));
    assert!(!xyz.member(&chars("abc")));
    assert!(!xyz.member(&chars("abcfff")));
    assert!(!xyz.member(&chars("kkk")));

    let abc_xyz = xyz.pre_image(abc_to_xyz);

    assert!(abc_xyz.member(&chars("xyz")));
    assert!(!abc_xyz.member(&chars("xyzfff")));
    assert!(abc_xyz.member(&chars("abc")));
    assert!(!abc_xyz.member(&chars("abcfff")));
    assert!(!abc_xyz.member(&chars("kkk")));
  }

  #[test]
  fn pre_image_replace_star_all() {
    let a_to_x = Builder::replace_all_reg(Regex::seq("a"), to_replacer("x"));

    let x_ = Regex::seq("x")
      .concat(Regex::all().star())
      .to_sym_fa::<StateImpl>();

    assert!(x_.member(&chars("x")));
    assert!(x_.member(&chars("xyzfff")));
    assert!(!x_.member(&chars("a")));
    assert!(!x_.member(&chars("ayzfff")));
    assert!(!x_.member(&chars("kkk")));

    let a_ = x_.pre_image(a_to_x);

    assert!(a_.member(&chars("x")));
    assert!(a_.member(&chars("xyzfff")));
    assert!(a_.member(&chars("a")));
    assert!(a_.member(&chars("ayzfff")));
    assert!(!a_.member(&chars("kkk")));
  }

  #[test]
  fn pre_image_replace_one() {
    let a_to_x = Builder::replace_reg(Regex::seq("a"), to_replacer("x"));

    let x = Regex::seq("x").to_sym_fa::<StateImpl>();

    assert!(x.member(&chars("x")));
    assert!(!x.member(&chars("xyzfff")));
    assert!(!x.member(&chars("a")));
    assert!(!x.member(&chars("ayzfff")));
    assert!(!x.member(&chars("kkk")));

    let a = x.pre_image(a_to_x);

    assert!(a.member(&chars("x")));
    assert!(!a.member(&chars("xyzfff")));
    assert!(a.member(&chars("a")));
    assert!(!a.member(&chars("ayzfff")));
    assert!(!a.member(&chars("kkk")));
  }

  #[test]
  fn pre_image_replace_concat() {
    let abc_to_xy = Builder::replace_reg(Regex::seq("abc"), to_replacer("xyz"));

    let xy = Regex::seq("xyz").to_sym_fa::<StateImpl>();

    assert!(xy.member(&chars("xyz")));
    assert!(!xy.member(&chars("xyzfff")));
    assert!(!xy.member(&chars("abc")));
    assert!(!xy.member(&chars("abcfff")));
    assert!(!xy.member(&chars("kkk")));

    let abc_xy = xy.pre_image(abc_to_xy);

    assert!(abc_xy.member(&chars("xyz")));
    assert!(!abc_xy.member(&chars("xyzfff")));
    assert!(abc_xy.member(&chars("abc")));
    assert!(!abc_xy.member(&chars("abcfff")));
    assert!(!abc_xy.member(&chars("kkk")));
  }

  #[test]
  fn pre_image_replace_star() {
    let a_to_x = Builder::replace_reg(Regex::seq("a"), to_replacer("x"));

    let x_ = Regex::seq("x")
      .concat(Regex::all().star())
      .to_sym_fa::<StateImpl>();

    assert!(x_.member(&chars("x")));
    assert!(x_.member(&chars("xyzfff")));
    assert!(!x_.member(&chars("a")));
    assert!(!x_.member(&chars("ayzfff")));
    assert!(!x_.member(&chars("kkk")));

    let a_ = x_.pre_image(a_to_x);

    assert!(a_.member(&chars("x")));
    assert!(a_.member(&chars("xyzfff")));
    assert!(a_.member(&chars("a")));
    assert!(a_.member(&chars("ayzfff")));
    assert!(!a_.member(&chars("kkk")));
  }
}
