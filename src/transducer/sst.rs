use super::term::{FunctionTerm, FunctionTermImpl, OutputComp, UpdateComp, Variable};
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::state::{self, State, StateMachine};
use crate::util::{
  extention::{ImmutableValueMap, MultiMap},
  Domain,
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
    Self {
      states,
      variables,
      initial_state,
      output_function,
      transition,
    }
    .minimize()
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
      &mut |(_, map), c, (q, alpha)| {
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
                OutputComp::X(x) => f.get(x).unwrap_or(&Vec::new()).clone(),
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

  /**
   * merging two sst.
   * output function is first one's,
   * and second one's is into the given result variable.
   * to say short, create a new sst that is based on first sst,
   * but have second one's info like transition, variables, output.
   * the sst will refuse a input if either one sst refuse it.
   */
  pub fn merge(self, other: Self, result: &V) -> Self {
    let error_msg = "Uncontrolled states exist. this will happen for developper's error";

    let Self {
      states: s1,
      mut variables,
      initial_state: i1,
      output_function: o1,
      transition: t1,
    } = self;

    let Self {
      states: s2,
      variables: v2,
      initial_state: i2,
      output_function: o2,
      transition: t2,
    } = other;

    let cartesian: HashMap<_, _> = s1
      .iter()
      .flat_map(|p| s2.iter().map(move |q| ((p, q), S::new())))
      .collect();

    let initial_state = S::clone(cartesian.get(&(&i1, &i2)).expect(error_msg));

    variables.extend(v2.into_iter());
    variables.insert(V::clone(result));

    let mut transition: Transition<B, F, S, V> = t1
      .iter()
      .flat_map(|((p1, phi1), v1)| {
        t2.iter()
          .map(|((p2, phi2), v2)| {
            let source = S::clone(cartesian.get(&(p1, p2)).expect(error_msg));
            let target = v1
              .into_iter()
              .flat_map(|(q1, u1)| {
                v2.into_iter()
                  .map(|(q2, u2)| {
                    let target = S::clone(cartesian.get(&(q1, q2)).expect(error_msg));

                    let update = u1
                      .iter()
                      .chain(u2.into_iter())
                      .map(|(v, uc)| (V::clone(&v), uc.clone()))
                      .collect();

                    (target, update)
                  })
                  .collect::<Vec<_>>()
              })
              .collect();

            ((source, phi1.and(phi2)), target)
          })
          .collect::<Vec<_>>()
      })
      .collect();

    let mut output_function = HashMap::new();
    o1.iter().for_each(|(fs1, output1)| {
      o2.iter().for_each(|(fs2, output2)| {
        let fs = cartesian.get(&(fs1, fs2)).expect(error_msg);

        output_function.insert(S::clone(fs), output1.clone());

        let target = transition
          .entry((S::clone(fs), B::char(D::separator())))
          .or_default();
        if target.is_empty() {
          let mut update_seq = vec![UpdateComp::X(V::clone(result))];
          update_seq.extend(super::to_update(output2));
          target.push((
            S::clone(fs),
            super::macros::make_update! {
              result -> update_seq
            },
          ));
        } else {
          target.iter_mut().for_each(|(_, update)| {
            let update_seq = update.entry(V::clone(result)).or_insert(vec![]);
            update_seq.extend(super::to_update(output2));
          });
        }
      });
    });

    let states = cartesian.into_values().collect();

    Self::new(
      states,
      variables,
      initial_state,
      output_function,
      transition,
    )
  }

  /*
   * mainly focus to use in my theory.
   * link them togeher and separating with T::separator
   */
  pub(crate) fn chain(self, other: Self) -> Self {
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
      output_function: o2,
      transition: t2,
    } = other;

    states.extend(s2.into_iter());
    variables.extend(v2.into_iter());
    let res_of_self = V::new();

    transition.extend(t2.into_iter());
    o1.into_iter().for_each(|(fs1, out)| {
      let target = transition
        .entry((fs1, B::char(D::separator())))
        .or_insert(vec![(S::clone(&i2), HashMap::new())]);
      target.iter_mut().for_each(|(s, u)| {
        *s = S::clone(&i2);
        u.safe_insert(V::clone(&res_of_self), super::to_update(&out));
      });
    });

    let output_function = o2
      .into_iter()
      .map(|(fs, output)| {
        (
          fs,
          [
            OutputComp::X(V::clone(&res_of_self)),
            OutputComp::A(D::separator()),
          ]
          .iter() //https://doc.rust-lang.org/nightly/edition-guide/rust-2021/IntoIterator-for-arrays.html
          .cloned()
          .chain(output.into_iter())
          .collect(),
        )
      })
      .collect();

    variables.insert(res_of_self);

    Self::new(
      states,
      variables,
      initial_state,
      output_function,
      transition,
    )
  }

  pub fn chain_output(self, output: Output<D, V>, vars: HashSet<V>) -> Self {
    self.chain(super::macros::sst! {
      { state },
      vars,
      { -> state },
      { state -> output }
    })
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
