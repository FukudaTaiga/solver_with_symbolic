use super::recognizable::Recognizable;
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::state::{self, State, StateMachine};
use crate::transducer::{
  sst::SymSst,
  term::{OutputComp, UpdateComp, Variable},
};
use crate::util::{extention::MultiMap, Domain};
use std::{
  collections::{BTreeMap, BTreeSet, HashMap, HashSet},
  fmt::Debug,
};

type Source<S, B> = (S, B);
type Target<S> = Vec<S>;

/*
 * https://stackoverflow.com/questions/32300132/why-cant-i-store-a-value-and-a-reference-to-that-value-in-the-same-struct
 * https://stackoverflow.com/questions/41270052/cannot-infer-an-appropriate-lifetime-for-autoref-due-to-conflicting-requirements
 * self-referential struct is unsafe in Rust - https://qiita.com/9laceef/items/aa0d7e1bd5041a1857d5
 * need to think deeply of an implementation if more efficient one
 */
/**
 * symbolic automata
 * each operation like concat, or, ... corresponds to regex's one.
 */
#[derive(Debug, PartialEq, Clone)]
pub struct SymFa<D, B, S>
where
  D: Domain,
  B: BoolAlg<Domain = D>,
  S: State,
{
  pub(crate) states: HashSet<S>,
  pub(crate) initial_state: S,
  pub(crate) final_states: HashSet<S>,
  pub(crate) transition: HashMap<Source<S, B>, Target<S>>,
}
impl<D, B, S> Default for SymFa<D, B, S>
where
  D: Domain,
  B: BoolAlg<Domain = D>,
  S: State,
{
  fn default() -> Self {
    /* default regex .* */
    super::macros::sfa! {
      { state },
      { -> state, (state, B::all_char()) -> [state] },
      { state }
    }
  }
}
impl<D, B, S> SymFa<D, B, S>
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

    let mut sfa = Self {
      states,
      initial_state,
      final_states,
      transition,
    };
    sfa.minimize();
    sfa
  }

  pub fn run<'a>(&self, input: impl IntoIterator<Item = &'a B::Domain>) -> bool
  where
    B::Domain: 'a,
  {
    self.generalized_run(
      input.into_iter(),
      vec![self.initial_state.clone()],
      |_, _, next| S::clone(next),
      |possibilities| {
        possibilities
          .into_iter()
          .find(|s| self.final_states.contains(s))
          .is_some()
      },
    )
  }

  pub fn accepted_path(self) -> Option<Vec<B>> {
    let mut result = None;
    let mut paths = vec![(self.initial_state(), vec![])];
    let mut visited = HashSet::new();
    while let Some((state, path)) = paths.pop() {
      if self.final_states.contains(state) {
        result = Some(path);
        break;
      }

      paths.extend(
        self
          .transition()
          .into_iter()
          .flat_map(|((p, phi), target)| {
            if *p == *state {
              let mut path = path.clone();
              path.push(phi.clone());
              target
                .into_iter()
                .filter_map(|q| (!visited.contains(q)).then(|| (q, path.clone())))
                .collect()
            } else {
              vec![]
            }
          }),
      );

      visited.insert(state);
    }

    result
  }

  pub fn concat(self, other: Self) -> Self {
    let Self {
      mut states,
      initial_state,
      final_states: f1,
      mut transition,
    } = self;

    let Self {
      states: s2,
      initial_state: i2,
      mut final_states,
      transition: t2,
    } = other;

    states.extend(s2.into_iter());

    t2.into_iter().for_each(|((state, phi), target)| {
      if state == i2 {
        f1.iter().for_each(|final_state| {
          transition.insert_with_check((S::clone(&final_state), phi.clone()), target.clone());
        });
      }
      transition.insert_with_check((state, phi), target);
    });

    if final_states.contains(&i2) {
      final_states.extend(f1.into_iter());
    }

    Self::new(states, initial_state, final_states, transition)
  }

  pub fn or(self, other: Self) -> Self {
    let Self {
      mut states,
      initial_state: i1,
      mut final_states,
      transition: t1,
    } = self;

    let Self {
      states: s2,
      initial_state: i2,
      final_states: f2,
      transition: t2,
    } = other;

    let initial_state = S::new();

    states.extend(s2.into_iter());
    states.insert(S::clone(&initial_state));

    final_states.extend(f2.into_iter());
    if final_states.contains(&i1) || final_states.contains(&i2) {
      final_states.insert(S::clone(&initial_state));
    }

    let mut transition = HashMap::new();
    t1.into_iter().for_each(|((state, phi), target)| {
      if state == i1 {
        transition.insert((S::clone(&initial_state), phi.clone()), target.clone());
      }
      transition.insert((state, phi), target);
    });
    t2.into_iter().for_each(|((state, phi), target)| {
      if state == i2 {
        transition.insert_with_check((S::clone(&initial_state), phi.clone()), target.clone());
      }
      transition.insert((state, phi), target);
    });

    Self::new(states, initial_state, final_states, transition)
  }

  pub fn inter(self, other: Self) -> Self {
    let error_msg = "Uncontrolled states exist. this will happen for developper's error";

    let Self {
      states: s1,
      initial_state: i1,
      final_states: f1,
      transition: t1,
    } = self;

    let Self {
      states: s2,
      initial_state: i2,
      final_states: f2,
      transition: t2,
    } = other;

    let cartesian: HashMap<_, _> = s1
      .iter()
      .flat_map(|p| s2.iter().map(move |q| ((p, q), S::new())))
      .collect();

    let final_states = cartesian
      .iter()
      .filter_map(|((p, q), s)| (f1.contains(*p) && f2.contains(*q)).then(|| S::clone(s)))
      .collect();

    let mut transition = HashMap::new();
    t1.iter().for_each(|((p1, phi1), target1)| {
      t2.iter().for_each(|((p2, phi2), target2)| {
        let p = S::clone(cartesian.get(&(p1, p2)).expect(error_msg));
        let target: Vec<_> = target1
          .into_iter()
          .flat_map(|s1| {
            target2
              .into_iter()
              .map(|s2| S::clone(cartesian.get(&(s1, s2)).expect(error_msg)))
              .collect::<Vec<_>>()
          })
          .collect();

        transition.insert_with_check((p, phi1.and(phi2)), target);
      })
    });

    let initial_state = S::clone(cartesian.get(&(&i1, &i2)).expect(error_msg));

    let states = cartesian.into_values().collect();

    Self::new(states, initial_state, final_states, transition)
  }

  pub fn not(self) -> Self {
    let not_predicates: HashMap<_, _> = self
      .states
      .iter()
      .map(|state| (S::clone(state), self.state_predicate(state).not()))
      .collect();

    let Self {
      mut states,
      initial_state,
      final_states,
      mut transition,
    } = self;

    let mut final_states = &states - &final_states;
    let dead_state = S::new();

    states.iter().for_each(|state| {
      transition.insert(
        (S::clone(state), not_predicates.get(state).unwrap().clone()),
        vec![S::clone(&dead_state)],
      );
    });
    transition.insert(
      (S::clone(&dead_state), B::top()),
      vec![S::clone(&dead_state)],
    );

    states.insert(S::clone(&dead_state));
    final_states.insert(dead_state);

    Self::new(states, initial_state, final_states, transition)
  }

  pub fn star(self) -> Self {
    let Self {
      mut states,
      initial_state: i,
      mut final_states,
      transition: t,
    } = self;

    let initial_state = S::new();
    states.insert(S::clone(&initial_state));
    final_states.insert(S::clone(&initial_state));

    let mut transition = HashMap::new();
    t.into_iter().for_each(|((state, phi), target)| {
      if state == i {
        final_states.iter().for_each(|final_state| {
          transition.insert_with_check((S::clone(final_state), phi.clone()), target.clone());
        });
        transition.insert((S::clone(&initial_state), phi.clone()), target.clone());
      }
      transition.insert((state, phi), target);
    });

    Self::new(states, initial_state, final_states, transition)
  }

  pub fn plus(self) -> Self {
    let Self {
      states,
      initial_state,
      final_states,
      transition: t,
    } = self;

    let mut transition = HashMap::new();
    t.into_iter().for_each(|((state, phi), target)| {
      if state == initial_state {
        final_states.iter().for_each(|final_state| {
          transition.insert_with_check((S::clone(final_state), phi.clone()), target.clone());
        });
        transition.insert((S::clone(&initial_state), phi.clone()), target.clone());
      }
      transition.insert((state, phi), target);
    });

    Self::new(states, initial_state, final_states, transition)
  }

  pub fn pre_image_forward<V: Variable>(self, sst: SymSst<D, B, B::Term, S, V>) -> Self {
    eprintln!("preimage");
    let mut states = HashMap::new();
    let mut initial_states = HashSet::new();
    let mut transition: HashMap<_, Vec<_>> = HashMap::new();
    let mut final_states = HashSet::new();

    let reachables: HashMap<_, _> = self
      .states()
      .into_iter()
      .map(|s| (s, self.reachables(s)))
      .collect();

    let mut stack = vec![];

    macro_rules! step_with_var {
      ( $possibilities:ident,
        $var_name:ident,
        $to_check:expr,
        | $curr:ident, $var_map:ident $(,$others:ident)* |
      ) => {
        $possibilities
          .into_iter()
          .flat_map(|($curr, $var_map, $($others),*)| {
            let target_states = reachables.get(&$curr).unwrap();

            target_states.into_iter().filter_map(|next| {
              $to_check.contains(next).then(|| {
                let mut var_map = $var_map.clone();
                let target = var_map.entry(($curr, $var_name)).or_insert(vec![]);
                if target.contains(next) {
                  (*next, var_map, $($others.clone()),*)
                } else {
                  target.push(next);
                  (*next, var_map, $($others.clone()),*)
                }
              })
            }).collect::<Vec<_>>()
          })
          .collect()
      };
    }

    {
      let to_check: HashSet<_> = self.states.iter().collect();

      for (q, output) in sst.final_set() {
        let mut possibilities = vec![(&self.initial_state, HashMap::new())];

        for oc in output {
          match oc {
            OutputComp::A(a) => {
              possibilities = self.step(possibilities, {
                |(curr, var_map), ((p1, phi), p2)| {
                  (*p1 == **curr && phi.denote(a) && to_check.contains(p2))
                    .then(|| (p2, var_map.clone()))
                }
              });
            }
            OutputComp::X(x) => {
              possibilities = step_with_var!(possibilities, x, to_check, |curr, var_map|);
            }
          }
        }

        possibilities.into_iter().for_each(|(p, var_map)| {
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
        });
      }
    }

    eprintln!(
      "stack {:?}\n\nstart searching, {}, vars: {}",
      stack,
      stack.len(),
      sst.variables().len()
    );

    while let Some(tuple) = stack.pop() {
      #[cfg(test)]
      {
        if states.len() > 200 {
          eprintln!("states: {:#?}", states);
          panic!("psedo stack overflow");
        }
      }

      let next = S::clone(states.get(&tuple).unwrap());
      let (q, var_map) = tuple;

      for ((q1, psi), target) in sst.transition() {
        'add_update: for (_, alpha) in target.into_iter().filter(|(s, _)| *s == *q) {
          let mut phi = HashMap::new();
          let mut pre_maps: HashMap<_, Vec<_>> = HashMap::new();

          for ((p1, var), nexts) in &var_map {
            let to_check: HashSet<_> = self
              .states
              .iter()
              .filter(|s| {
                reachables
                  .get(s)
                  .unwrap()
                  .iter()
                  .find(|s| nexts.contains(s))
                  .is_some()
              })
              .collect();
            let mut possibilities = vec![(*p1, HashMap::new(), B::top())];

            if let Some(seq) = alpha.get(*var) {
              for uc in seq.into_iter() {
                match uc {
                  UpdateComp::F(lambda) => {
                    possibilities = self.step(possibilities, {
                      |(curr, var_map, var_phi), ((r1, phi), r2)| {
                        (*r1 == **curr && to_check.contains(r2))
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
                    possibilities =
                      step_with_var!(possibilities, x, to_check, |curr, var_map, var_phi|);
                  }
                }
              }
            } else {
              /*
               * if update function has no corresponding output, update with identity function
               * i.e. update(var) = vec![UpdateComp::X(var)]
               */
              possibilities = nexts
                .into_iter()
                .map(|next| (*next, HashMap::from([((*p1, *var), vec![*next])]), B::top()))
                .collect();
            }

            /*
             * if both sst and sfa are minimized, nexts.len() != 0. it cannot panic
             * if nexts.len() over 64, then it will not working => check possibilities consists of all of nexts with iterator.
             */
            assert!(nexts.len() != 0 && nexts.len() < 64);
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
              possibilities.into_iter().for_each(|(p, var_map, var_phi)| {
                let p_phi = phi.entry((*p1, *var, p)).or_insert(B::bot());
                *p_phi = p_phi.or(&var_phi);
                pre_maps.insert_with_check(*var, [var_map]);
              })
            } else {
              continue 'add_update;
            }
          }

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

            pre_maps.into_iter().for_each(|pre_map| {
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
            });
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

    #[cfg(test)]
    {
      eprintln!("finish searching");
      eprintln!("states map:\n{:#?}", states);
      eprintln!("transition:\n{:#?}", transition);
    }

    let mut states: HashSet<_> = states.into_values().collect();
    let initial_state = S::new();

    states.insert(S::clone(&initial_state));

    let transition_ = transition;
    let mut transition = HashMap::new();

    transition_.into_iter().for_each(|((state, phi), target)| {
      if initial_states.contains(&state) {
        transition.insert_with_check((S::clone(&initial_state), phi.clone()), target.clone());
      }
      transition.insert((state, phi), target);
    });

    if initial_states.intersection(&final_states).next().is_some() {
      final_states.insert(S::clone(&initial_state));
    }

    if initial_states.is_empty() {
      Self::empty()
    } else {
      Self::new(states, initial_state, final_states, transition)
    }
  }

  pub fn pre_image<V: Variable>(self, sst: SymSst<D, B, B::Term, S, V>) -> Self {
    #[cfg(test)]
    eprintln!("preimage");

    let mut states = HashMap::new();
    let mut initial_states = HashSet::new();
    let mut transition: HashMap<_, Vec<_>> = HashMap::new();
    let mut final_states = HashSet::new();

    let reachable_sources: HashMap<_, _> = self
      .states()
      .into_iter()
      .map(|s| (s, self.reachable_sources(s)))
      .collect();

    let mut stack = vec![];

    macro_rules! back_with_var {
      ( $possibilities:ident,
        $var_name:ident,
        $to_check:expr,
        | $curr:ident, $var_map:ident $(,$others:ident)* |
      ) => {
        $possibilities
          .into_iter()
          .flat_map(|($curr, $var_map, $($others),*)| {
            let sources = reachable_sources.get(&$curr).unwrap();

            sources.into_iter().filter_map(|source| {
              $to_check.contains(source).then(|| {
                let mut var_map = $var_map.clone();
                let target = var_map.entry($var_name).or_insert(BTreeSet::new());
                if target.contains(&(*source, $curr)) {
                  (*source, var_map, $($others.clone()),*)
                } else {
                  target.insert((*source, $curr));
                  (*source, var_map, $($others.clone()),*)
                }
              })
            }).collect::<Vec<_>>()
          })
          .collect()
      };
    }

    {
      let to_check: HashSet<_> = self.states.iter().collect();

      for (q, output) in sst.final_set() {
        let mut possibilities = self
          .final_states
          .iter()
          .map(|fs| (fs, BTreeMap::new()))
          .collect();

        for oc in output.into_iter().rev() {
          match oc {
            OutputComp::A(a) => {
              possibilities = self.back(
                possibilities,
                |(curr, var_map), ((p1, _), p2)| (*p2 == **curr).then(|| (p1, var_map.clone())),
                |(_, phi)| phi.denote(a),
              );
            }
            OutputComp::X(x) => {
              possibilities = back_with_var!(possibilities, x, to_check, |curr, var_map|);
            }
          }
        }

        possibilities.into_iter().for_each(|(p, var_map)| {
          if *p == self.initial_state {
            let tuple = (q, var_map);
            stack.push(tuple.clone());
            if let None = states.get(&tuple) {
              let new_state = S::new();
              final_states.insert(S::clone(&new_state));
              states.insert(tuple, new_state);
            }
          }
        });
      }
    }

    #[cfg(test)]
    {
      eprintln!(
        "start searching.\nstack_len: {}, vars_len: {}",
        stack.len(),
        sst.variables().len()
      );
    }

    while let Some(tuple) = stack.pop() {
      #[cfg(test)]
      {
        if states.len() > 5000 {
          eprintln!("states: {:#?}", states);
          panic!("psedo stack overflow");
        }
      }

      let next = S::clone(states.get(&tuple).unwrap());
      let (q, var_map) = tuple;

      for ((q1, psi), target) in sst.transition() {
        'add_update: for (_, alpha) in target.into_iter().filter(|(s, _)| *s == *q) {
          let mut phi = HashMap::new();
          let mut pre_maps: HashMap<_, Vec<_>> = HashMap::new();

          for (var, nexts) in &var_map {
            for (p1, p2) in nexts {
              let to_check = reachable_sources.get(p2).unwrap();
              let mut possibilities = vec![(*p2, BTreeMap::new(), B::top())];

              if let Some(seq) = alpha.get(*var) {
                for uc in seq.into_iter().rev() {
                  match uc {
                    UpdateComp::F(lambda) => {
                      possibilities = self.back(
                        possibilities,
                        |(curr, var_map, var_phi), ((r1, phi), r2)| {
                          (*r2 == **curr)
                            .then(|| var_phi.and(&phi.with_lambda(lambda)))
                            .and_then(|var_phi| {
                              var_phi
                                .satisfiable()
                                .then(|| (r1, var_map.clone(), var_phi))
                            })
                        },
                        |(r1, _)| to_check.contains(r1),
                      );
                    }
                    UpdateComp::X(x) => {
                      possibilities =
                        back_with_var!(possibilities, x, to_check, |curr, var_map, var_phi|);
                    }
                  }
                }
              } else {
                /*
                 * if update function has no corresponding output, update with identity function
                 * i.e. update(var) = vec![UpdateComp::X(var)]
                 */
                possibilities = vec![(
                  p1,
                  BTreeMap::from([(*var, BTreeSet::from([(*p1, *p2)]))]),
                  B::top(),
                )];
              }

              possibilities = possibilities
                .into_iter()
                .filter(|(p, _, _)| *p == *p1)
                .collect();

              if possibilities.len() != 0 {
                possibilities.into_iter().for_each(|(_, var_map, var_phi)| {
                  let p_phi = phi.entry((*p1, *var, *p2)).or_insert(B::bot());
                  *p_phi = var_phi.or(p_phi);
                  pre_maps.insert_with_check(*var, [var_map]);
                });
              } else {
                continue 'add_update;
              }
            }
          }

          let phi = phi
            .into_values()
            .reduce(|phi, p_phi| phi.and(&p_phi))
            .unwrap_or(B::boolean(var_map.is_empty()))
            .and(psi);

          if phi.satisfiable() {
            /* calculate each combination of pre_maps */
            let pre_maps = {
              let mut combination = vec![BTreeMap::new()];

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

            pre_maps.into_iter().for_each(|pre_map| {
              let tuple = (q1, pre_map);
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
            });
          }
        }
      }

      let is_initial = var_map
        .iter()
        .all(|(_, nexts)| nexts.into_iter().all(|(p1, p2)| **p1 == **p2));

      if *q == *sst.initial_state() && is_initial {
        initial_states.insert(next);
      }
    }

    #[cfg(test)]
    {
      eprintln!("finish searching");
      eprintln!("states map:\n{:#?}", states);
      eprintln!("transition:\n{:#?}", transition);
    }

    let mut states: HashSet<_> = states.into_values().collect();
    let initial_state = S::new();

    states.insert(S::clone(&initial_state));

    let transition_ = transition;
    let mut transition = HashMap::new();

    transition_.into_iter().for_each(|((state, phi), target)| {
      if initial_states.contains(&state) {
        transition.insert_with_check((S::clone(&initial_state), phi.clone()), target.clone());
      }
      transition.insert((state, phi), target);
    });

    if initial_states.intersection(&final_states).next().is_some() {
      final_states.insert(S::clone(&initial_state));
    }

    if initial_states.is_empty() {
      Self::empty()
    } else {
      Self::new(states, initial_state, final_states, transition)
    }
  }

  pub fn chain(self, other: Self) -> Self {
    let Self {
      mut states,
      initial_state,
      final_states: joint_out,
      mut transition,
    } = self;

    let Self {
      states: states_,
      initial_state: joint_in,
      final_states,
      transition: transition_,
    } = other;

    states.extend(states_);
    transition.extend(transition_);

    for joint in joint_out {
      transition.insert_with_check((joint, B::separator()), [S::clone(&joint_in)]);
    }

    Self::new(states, initial_state, final_states, transition)
  }

  pub fn finish(self) -> Self {
    self.concat(super::macros::sfa! {
      { dead, joint },
      { -> dead, (dead, B::char(D::separator())) -> [joint] },
      { joint }
    })
  }
}
impl<D, B, S> Recognizable<D> for SymFa<D, B, S>
where
  D: Domain,
  B: BoolAlg<Domain = D>,
  S: State,
{
  fn member(&self, input: &[B::Domain]) -> bool {
    self.run(input)
  }
}
impl<D, B, S> StateMachine for SymFa<D, B, S>
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

pub type Sfa<T, S> = SymFa<T, Predicate<T>, S>;

#[cfg(test)]
mod tests {
  use super::super::regex::Regex;
  use super::*;
  use crate::transducer::sst_factory::SstBuilder;
  use crate::util::CharWrap;
  use crate::{boolean_algebra::Predicate, tests::helper::*};

  type Builder = SstBuilder<CharWrap, StateImpl, VariableImpl>;
  type Reg = Regex<CharWrap>;

  macro_rules! basics {
    (
      names: [$id:ident, $cnst:ident, $rev:ident],
      reg: $reg:expr,
      id: {
        accepts: [$( $id_ac:expr ),*],
        rejects: [$( $id_re:expr ),*]
      },
      constant: $constant:expr => {
        accepts: [$( $cnst_ac:expr ),*], /* inputs havent been changed */
        rejects: [$( $cnst_re:expr ),*]
      },
      rev: {
        accepts: [$( $rev_ac:expr ),*], /* inputs havent been changed */
        rejects: [$( $rev_re:expr ),*]
      }
    ) => {
      #[test]
      fn $id() {
        let sst = Builder::identity(&VariableImpl::new());
        let sfa = $reg.to_sfa();
        eprintln!("sfa: {:?}", sfa);
        $( assert!(sfa.run(&chars($id_ac))); )*
        $( assert!(!sfa.run(&chars($id_re))); )*
        let pre_image = sfa.pre_image(sst);
        eprintln!("preimage: {:?}", pre_image);
        $( assert!(pre_image.run(&chars($id_ac))); )*
        $( assert!(!pre_image.run(&chars($id_re))); )*
      }

      #[test]
      fn $cnst() {
          let sst = Builder::constant($constant);
          let sfa = $reg.to_sfa();
          eprintln!("sfa: {:?}", sfa);
          let pre_image = sfa.pre_image(sst);
          eprintln!("preimage: {:?}", pre_image);
          $( assert!(pre_image.run(&chars($cnst_ac))); )*
          $( assert!(!pre_image.run(&chars($cnst_re))); )*
      }

      #[test]
      fn $rev() {
          let sst = Builder::reverse(&VariableImpl::new());
          let sfa = $reg.to_sfa();
          eprintln!("sfa: {:?}", sfa);
          let pre_image = sfa.pre_image(sst);
          eprintln!("preimage: {:?}", pre_image);
          $( assert!(pre_image.run(&chars($rev_ac))); )*
          $( assert!(!pre_image.run(&chars($rev_re))); )*
      }
    };
  }

  macro_rules! replace_tests {
    (
      names: [$name:ident, $name_all:ident],
      from: $from:expr,
      to: $to:expr,
      reg: $reg:expr,
      $(
        ensure: {
          accepts: [ $( $sfa_ac:expr ),* ],
          rejects: [ $( $sfa_re:expr ),* ]
        },
      )?
      accepts: [ $( $accept:expr ),* ], /* inputs havent been replaced */
      rejects: [ $( $reject:expr ),* ]
    ) => {
      #[test]
      fn $name() {
        let sst = Builder::replace_reg(Regex::seq($from), to_replacer($to));
        let sfa = $reg.to_sfa();
        eprintln!("sfa: {:?}", sfa);
        $(
          $( assert!(sfa.run(&chars($sfa_ac))); )*
          $( assert!(!sfa.run(&chars($sfa_re))); )*
        )?
        let pre_image = sfa.pre_image(sst);
        eprintln!("preimage: {:?}", pre_image);
        $( assert!(pre_image.run(&chars(&$accept.replacen($from, $to, 1)))); )+
        $( assert!(!pre_image.run(&chars(&$reject.replacen($from, $to, 1)))); )+
      }

      #[test]
      fn $name_all() {
        let sst = Builder::replace_all_reg(Regex::seq($from), to_replacer($to));
        let sfa = $reg.to_sfa();
        eprintln!("sfa: {:?}", sfa);
        let pre_image = sfa.pre_image(sst);
        eprintln!("preimage: {:?}", pre_image);
        $( assert!(pre_image.run(&chars(&$accept.replace($from, $to)))); )+
        $( assert!(!pre_image.run(&chars(&$reject.replace($from, $to)))); )+
      }
    };
  }

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
      type GetOne = T;

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
      fn get_one(self) -> Result<Self::Domain, crate::boolean_algebra::NoElement> {
        unimplemented!()
      }
    }
    impl<T: Domain, S: State> From<Sfa<T, S>> for SymFa<T, RegexPredicate<T>, S> {
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
    impl<T: Domain, S: State> SymFa<T, RegexPredicate<T>, S> {
      /** assuming given sfa has been minimized */
      pub fn to_reg(mut self) -> Regex<T> {
        if self.states.len() == 0 {
          unreachable!()
        } else if self.states.len() == 1 {
          Regex::empty()
        } else if self.states.len() == 2 {
          self.minimize();
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

    let sym_fa = SymFa::new(
      states.clone(),
      initial_state.clone(),
      final_states.clone(),
      transition.clone(),
    );
    eprintln!("{:#?}", sym_fa);
    assert_eq!(sym_fa.states.len(), 2);
    assert!(sym_fa.run(&chars("afvfdl")));
    assert!(!sym_fa.run(&chars("")));
    assert!(sym_fa.run(&chars("awa")));
    assert!(sym_fa.run(&chars("cwbwad")));
    assert!(!sym_fa.run(&chars("cwbwadww")));

    let sym_fa = SymFa {
      states,
      initial_state,
      final_states,
      transition,
    };
    eprintln!("{:#?}", sym_fa);
    assert_eq!(sym_fa.states.len(), 3);
    assert!(sym_fa.run(&chars("afvfdl")));
    assert!(!sym_fa.run(&chars("")));
    assert!(sym_fa.run(&chars("awa")));
    assert!(sym_fa.run(&chars("cwbwad")));
    assert!(!sym_fa.run(&chars("cwbwadww")));
  }

  basics! {
    names: [pre_image_id_1, pre_image_cnst_1, pre_image_rev_1],
    reg: Regex::seq("xyz")
      .or(Regex::range(Some('o'), Some('r')).star()),
    id: {
      accepts: ["xyz", "ooqppq", ""],
      rejects: ["xyz___ddd", "opqr", "abcdefg"]
    },
    constant: "xyz" => {
      accepts: ["xyz", "", "opqr", "abcdefg"],
      rejects: []
    },
    rev: {
      accepts: ["zyx", "ooqppq", "qppqoo", ""],
      rejects: ["xyz", "opqr", "abcdefg"]
    }
  }

  basics! {
    names: [pre_image_id_2, pre_image_cnst_2, pre_image_rev_2],
    reg: Regex::seq("abc")
      .concat(Regex::element('x').or(Regex::element('y')).star()),
    id: {
      accepts: ["abc", "abcxyxyxy", "abcxx", "abcy"],
      rejects: ["a", "ab", "xyz___ddd", "abcdefg", "abcxyxyxyz", ""]
    },
    constant: "abcd" => {
      accepts: [],
      rejects: ["abc", "abcxyxyxy", "abcxx", "abcy", "xyz___ddd"]
    },
    rev: {
      accepts: ["cba", "xxcba", "yyxyxyxcba", "ycba"],
      rejects: ["abc", "ab", "cb", "c", "abcdefg", "kkk", "xxx", "y"]
    }
  }

  basics! {
    names: [pre_image_id_3, pre_image_cnst_3, pre_image_palindrome],
    reg: Reg::seq("abc").concat(Reg::all().star()).concat(Reg::seq("cba")),
    id: {
      accepts: ["abccba", "abcxyxyxycba", "abcsqpalcba", "abcycba"],
      rejects: ["a", "ab", "abccb", "bccba", "xyz___ddd", "abcdefgba", "axyxyxyza", ""]
    },
    constant: "abcd" => {
      accepts: [],
      rejects: ["abccba", "abcxyxyxycba", "abcsqpalcba", "abcycba", "xyzcba"]
    },
    rev: {
      accepts: ["abccba", "abcxyxyxycba", "abcsqpalcba", "abcycba"],
      rejects: ["a", "ab", "abccb", "bccba", "xyz___ddd", "abcdefgba", "axyxyxyza", ""]
    }
  }

  replace_tests! {
    names: [pre_image_replace_one, pre_image_replace_one_all],
    from: "a",
    to: "x",
    reg: Reg::seq("x"),
    ensure: {
      accepts: ["x"],
      rejects: ["xyz", "abc", "kkk", "s"]
    },
    accepts: ["x", "a"],
    rejects: ["xyz", "abc", "kkk", "s"]
  }

  replace_tests! {
    names: [pre_image_replace_concat, pre_image_replace_concat_all],
    from: "abc",
    to: "xyz",
    reg: Reg::seq("xyz"),
    ensure: {
      accepts: ["xyz"],
      rejects: ["xyzzfff", "abc", "abcfff", "kkk"]
    },
    accepts: ["xyz", "abc"],
    rejects: ["xyzfff", "abcfff", "kkk"]
  }

  replace_tests! {
    names: [pre_image_replace_star, pre_image_replace_star_all],
    from: "a",
    to: "x",
    reg: Reg::seq("x").concat(Reg::all().star()),
    ensure: {
      accepts: ["x", "xyzfff"],
      rejects: ["a", "abc", "abcfff", "kkk"]
    },
    accepts: ["x", "xyzfff", "a", "abc", "abcfff"],
    rejects: ["kkk"]
  }

  #[test]
  fn reachables() {
    type S = StateImpl;
    let sfa = super::super::macros::sfa! {
      { start, s1, s2, cycle, s3, end },
      {
        -> start,
        (start, Predicate::char('a')) -> [s1],
        (start, Predicate::top()) -> [s2, cycle],
        (cycle, Predicate::top()) -> [cycle, s2],
        (s2, Predicate::top()) -> [s3],
        (s1, Predicate::top()) -> [s3],
        (s3, Predicate::range(None, Some('x'))) -> [end],
        (end, Predicate::top()) -> [cycle]
      },
      { end }
    };

    assert_eq!(sfa.final_set().len(), 1);

    let end = sfa.final_set().iter().next().unwrap();

    let from_end = sfa.reachables(end);

    /* cycle, s2, s3, end */
    assert_eq!(from_end.len(), 4);
  }

  #[test]
  fn reverse_of_reverse_is_identity() {
    let sst = Builder::reverse(&VariableImpl::new());
    let accepts = [
      "atoxa",
      "atoxpappappappapf",
      "atoxpappappapd",
      &format!("atox{}x", "pap".repeat(100)),
    ];
    let rejects = [
      "atoxaa",
      "atoxapappappappapf",
      "atoxpapfpapssssssssssssssssssssssssssss",
      "atoxpfappappapd",
      "astoxpappaps",
      "atoxpappappapda",
      "xxx",
      "",
    ];
    let sfa = Reg::seq("atox")
      .concat(Reg::seq("pap").star())
      .concat(Reg::all())
      .to_sfa::<StateImpl>();
    for accept in &accepts {
      eprintln!("{}", accept);
      assert!(sfa.run(&chars(accept)));
    }
    for reject in &rejects {
      eprintln!("{}", reject);
      assert!(!sfa.run(&chars(reject)));
    }
    let sfa = sfa.pre_image(sst.clone());
    for accept in &accepts {
      eprintln!("{}", accept);
      assert!(sfa.run(&chars(&accept.chars().rev().collect::<String>())));
    }
    for reject in &rejects {
      eprintln!("{}", reject);
      assert!(!sfa.run(&chars(&reject.chars().rev().collect::<String>())));
    }
    let sfa = sfa.pre_image(sst);
    for accept in &accepts {
      eprintln!("{}", accept);
      assert!(sfa.run(&chars(&accept)));
    }
    for reject in &rejects {
      eprintln!("{}", reject);
      assert!(!sfa.run(&chars(&reject)));
    }
  }

  #[test]
  fn chain() {
    let sfa: SymFa<_, _, StateImpl> = Reg::seq("pre").to_sfa().chain(Reg::seq("suf").to_sfa());

    assert!(sfa.run(&vec![
      CharWrap::Char('p'),
      CharWrap::Char('r'),
      CharWrap::Char('e'),
      CharWrap::Separator,
      CharWrap::Char('s'),
      CharWrap::Char('u'),
      CharWrap::Char('f')
    ]));
    assert!(!sfa.run(&vec![CharWrap::Separator,]));
    assert!(!sfa.run(&vec![CharWrap::Separator, CharWrap::Separator,]));
    assert!(!sfa.run(&vec![
      CharWrap::Char('p'),
      CharWrap::Char('r'),
      CharWrap::Char('e'),
    ]));
    assert!(!sfa.run(&vec![
      CharWrap::Char('p'),
      CharWrap::Char('r'),
      CharWrap::Char('e'),
      CharWrap::Char('s'),
      CharWrap::Char('u'),
      CharWrap::Char('f')
    ]));
  }

  #[test]
  fn thesis_demo() {
    use crate::boolean_algebra::*;
    use crate::transducer::{
      macros,
      term::{FunctionTerm, Lambda, VariableImpl},
    };
    type S = StateImpl;
    type V = VariableImpl;
    type P = Predicate<char>;
    type L = Lambda<P>;
    let (x, y) = (VariableImpl::new(), VariableImpl::new());
    let sst = macros::sst! {
      {p},
      HashSet::from([x, y]),
      {
        -> p,
        (p, P::top()) -> [(p, macros::make_update! [
          x -> vec![UpdateComp::X(x.clone()), UpdateComp::F(L::identity())],
          y -> vec![UpdateComp::F(L::identity()), UpdateComp::X(y.clone())]
        ])]
      },
      {
        p -> vec![OutputComp::X(y.clone()), OutputComp::X(x.clone())]
      }
    };
    let sfa = super::super::macros::sfa! {
      { s1, s2, s3 },
      {
        -> s1,
        (s1, P::char('a')) -> [s2],
        (s1, P::char('a').not()) -> [s3],
        (s2, P::top()) -> [s2],
        (s3, P::top()) -> [s3]
      },
      { s2 }
    };

    eprintln!("sfa {:?}", sfa);
    eprintln!("sst {:?}", sst);
    let pre_image = sfa.pre_image(sst);
    eprintln!("preimage\n{:#?}", pre_image);
    assert!(pre_image.run(&"abca".chars().collect::<Vec<_>>()));
    assert!(pre_image.run(&"a".chars().collect::<Vec<_>>()));
    assert!(pre_image.run(&"zzzza".chars().collect::<Vec<_>>()));
    assert!(!pre_image.run(&"zzzz".chars().collect::<Vec<_>>()));
    assert!(!pre_image.run(&"abc".chars().collect::<Vec<_>>()));
    assert!(!pre_image.run(&"x".chars().collect::<Vec<_>>()));
  }
}
