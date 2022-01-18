use super::term::{FunctionTerm, FunctionTermImpl, OutputComp, UpdateComp, Variable};
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::state::{self, State, StateMachine};
use crate::util::{
  Domain,
  extention::{ImmutableValueMap}
};
use std::{
  collections::{HashMap, HashSet},
  fmt::Debug,
};

type UpdateFunction<F, V> = HashMap<V, Vec<UpdateComp<F, V>>>;
type Source<B, S> = (S, B);
type Target<F, S, V> = (S, UpdateFunction<F, V>);
type Output<D, V> = Vec<OutputComp<D, V>>;
type Transition<B, F, S, V> = HashMap<Source<B, S>, Vec<Target<F, S, V>>>;

/** implementation of symbolic streaming string transducer (SSST) */
#[derive(Debug, PartialEq, Clone)]
pub struct SymSst<D, B, F, S, V>
where
  D: Domain,
  B: BoolAlg<Domain = D>,
  F: FunctionTerm<Domain = D>,
  S: State,
  V: Variable,
{
  pub(crate) states: HashSet<S>,
  pub(crate) variables: HashSet<V>,
  pub(crate) initial_state: S,
  pub(crate) output_function: HashMap<S, Output<D, V>>,
  /**
   * if a next transition has no correponding sequence for some variable, update with identity
   * i.e. update(var) = vec![UpdateComp::X(var)]
   */
  pub(crate) transition: Transition<B, F, S, V>,
}
impl<D, B, F, S, V> SymSst<D, B, F, S, V>
where
  D: Domain,
  B: BoolAlg<Domain = D>,
  F: FunctionTerm<Domain = D>,
  S: State,
  V: Variable,
{
  pub fn new(
    states: HashSet<S>,
    variables: HashSet<V>,
    initial_state: S,
    output_function: HashMap<S, Output<D, V>>,
    transition: Transition<B, F, S, V>,
  ) -> Self {
    let mut sst = Self {
      states,
      variables,
      initial_state,
      output_function,
      transition,
    };
    sst.minimize();
    sst
  }

  /**
   * execute sst with given input.
   * if a next transition has no correponding sequence for some variable,
   * deal with as if the transition translates it identically (i.e. x = x)
   */
  pub fn run<'a>(&self, input: impl IntoIterator<Item = &'a D>) -> Vec<Vec<D>>
  where
    D: 'a,
  {
    let initial_map: HashMap<V, Vec<D>> = self
      .variables
      .iter()
      .map(|var| (V::clone(var), vec![]))
      .collect();

    self.generalized_run(
      input.into_iter(),
      vec![(S::clone(&self.initial_state), initial_map)],
      |(_, map), c, (q, alpha)| {
        let var_map = self
          .variables
          .iter()
          .map(|var| {
            (
              V::clone(var),
              alpha
                .get(var)
                .unwrap_or(&vec![UpdateComp::X(V::clone(var))])
                .into_iter()
                .flat_map(|out| match out {
                  UpdateComp::F(f) => vec![D::clone(f.apply(c))],
                  UpdateComp::X(var) => map.get(var).unwrap_or(&vec![]).clone(),
                })
                .collect(),
            )
          })
          .collect();

        (S::clone(q), var_map)
      },
      |possibilities| {
        let mut results = vec![];
        possibilities.into_iter().for_each(|(q, f)| {
          if let Some(output) = self.output_function.get(&q) {
            let result = output
              .into_iter()
              .flat_map(|o| match o {
                OutputComp::A(a) => vec![D::clone(a)],
                OutputComp::X(x) => f.get(x).unwrap_or(&vec![]).clone(),
              })
              .collect();

            if !results.contains(&result) {
              results.push(result);
            }
          }
        });
        results
      },
    )
  }

  pub fn variables(&self) -> &HashSet<V> {
    &self.variables
  }

  pub fn variables_mut(&mut self) -> &mut HashSet<V> {
    &mut self.variables
  }

  /**
   * merging two sst.
   * output function is first one's,
   * and second one's is into the given result variable.
   * if result -> seq exists, concatenate output2 on it.
   * to say short, create a new sst that is based on first sst,
   * but have second one's info like transition, variables, output.
   * the sst will refuse a input if either one sst does.
   */
  pub(crate) fn merge(&mut self, other: Self, result: &V) {
    let error_msg = "Uncontrolled states exist. this will happen for developper's error";

    let Self {
      states: s2,
      variables: v2,
      initial_state: i2,
      output_function: o2,
      transition: t2,
    } = other;

    let cartesian: HashMap<_, _> = self
      .states
      .iter()
      .flat_map(|p| s2.iter().map(move |q| ((p, q), S::new())))
      .collect();

    let mut transition: Transition<B, F, S, V> = self
      .transition
      .iter()
      .flat_map(|((p1, phi1), target1)| {
        t2.iter()
          .filter_map(|((p2, phi2), target2)| {
            let phi = phi1.and(phi2);

            phi.satisfiable().then(|| {
              let p = S::clone(cartesian.get(&(p1, p2)).expect(error_msg));
              let target = target1
                .into_iter()
                .flat_map(|(q1, update1)| {
                  target2
                    .into_iter()
                    .map(|(q2, update2)| {
                      let q = S::clone(cartesian.get(&(q1, q2)).expect(error_msg));

                      let mut update = HashMap::with_capacity(update1.len() + update2.len());
                      update1.into_iter().for_each(|(var, seq)| {
                        update.insert(V::clone(var), seq.clone());
                      });
                      update2.into_iter().for_each(|(var, seq)| {
                        update.safe_insert(V::clone(var), seq.clone());
                      });

                      (q, update)
                    })
                    .collect::<Vec<_>>()
                })
                .collect();

              ((p, phi), target)
            })
          })
          .collect::<Vec<_>>()
      })
      .collect();

    let mut output_function = HashMap::new();
    self.output_function.iter().for_each(|(fs1, output1)| {
      o2.iter().for_each(|(fs2, output2)| {
        let fs = cartesian.get(&(fs1, fs2)).expect(error_msg);

        output_function.safe_insert(S::clone(fs), output1.clone());

        let target = transition
          .entry((S::clone(fs), B::separator()))
          .or_insert(vec![(S::clone(fs), HashMap::new())]);
        target.iter_mut().for_each(|(_, update)| {
          let update_seq = update
            .entry(V::clone(result))
            .or_default();
          update_seq.extend(super::to_update(output2));
        });
      });
    });

    let initial_state = S::clone(
      cartesian
        .get(&(self.initial_state(), &i2))
        .expect(error_msg),
    );

    self.states = cartesian.into_values().collect();
    self.initial_state = initial_state;
    self.variables.extend(v2.into_iter());
    self.variables.insert(V::clone(result));
    self.transition = transition;
    self.output_function = output_function;
  }

  /* mainly focus to use in my theory. */
  pub(crate) fn chain(self, other: Self, var: &V) -> Self {
    let Self {
      mut states,
      mut variables,
      initial_state,
      output_function: o1,
      mut transition,
    } = self;

    let Self {
      states: s2,
      variables: v2,
      initial_state: i2,
      output_function,
      transition: t2,
    } = other;

    states.extend(s2.into_iter());
    variables.extend(v2.into_iter());
    variables.insert(V::clone(var));

    t2.into_iter().for_each(|((p, phi), target)| {
      transition.safe_insert((p, phi), target)
    });
    o1.into_iter().for_each(|(fs1, out)| {
      let target = transition
        .entry((fs1, B::separator()))
        .or_insert(vec![(S::clone(&i2), HashMap::new())]);
      target.iter_mut().for_each(|(s, update)| {
        *s = S::clone(&i2);
        let seq = update.entry(V::clone(var)).or_default();
        seq.extend(super::to_update(&out));
        seq.push(UpdateComp::F(F::separator()));
      });
    });

    Self::new(
      states,
      variables,
      initial_state,
      output_function,
      transition,
    )
  }

  pub fn chain_output(self, output: Output<D, V>) -> Self {
    let Self {
      mut states,
      variables,
      initial_state,
      output_function: transition_,
      mut transition,
    } = self;

    let end = S::new();

    states.insert(S::clone(&end));
    transition_.into_iter().for_each(|(fs, _)| {
      let target = transition
        .entry((fs, B::separator()))
        .or_insert(vec![(S::clone(&end), HashMap::new())]);
      target.iter_mut().for_each(|(s, _)| {
        *s = S::clone(&end);
      });
    });

    let output_function = HashMap::from([(end, output)]);

    Self::new(
      states,
      variables,
      initial_state,
      output_function,
      transition,
    )
  }
}
impl<D, B, F, S, V> StateMachine for SymSst<D, B, F, S, V>
where
  D: Domain,
  B: BoolAlg<Domain = D>,
  F: FunctionTerm<Domain = D>,
  S: State,
  V: Variable,
{
  type StateType = S;
  type BoolAlg = B;
  type Target = Target<F, S, V>;
  type FinalState = (S, Output<D, V>);
  type FinalSet = HashMap<S, Output<D, V>>;

  fn empty() -> Self {
    let state = S::new();
    Self {
      states: HashSet::from([S::clone(&state)]),
      variables: HashSet::new(),
      initial_state: S::clone(&state),
      output_function: HashMap::from([(S::clone(&state), vec![])]),
      transition: HashMap::from([((S::clone(&state), B::top()), vec![(state, HashMap::new())])]),
    }
  }

  state::macros::impl_state_machine!(states, initial_state, output_function, transition);
}

pub type Sst<T, S, V> = SymSst<T, Predicate<T>, FunctionTermImpl<T>, S, V>;
