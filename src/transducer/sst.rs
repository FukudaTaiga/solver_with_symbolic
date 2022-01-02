use super::term::{FunctionTerm, FunctionTermImpl, Lambda, OutputComp, UpdateComp, Variable};
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::state::{State, StateMachine, self};
use crate::util::Domain;
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
pub struct SymSST<D, B, F, S, V>
where
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
impl<D, B, F, S, V> SymSST<D, B, F, S, V>
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
      vec![(self.initial_state.clone(), initial_map)],
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
        possibilities
          .into_iter()
          .filter_map(|(q, f)| {
            self.output_function.get(&q).map(|w| {
              w.iter()
                .flat_map(|o| match o {
                  OutputComp::A(a) => vec![D::clone(a)],
                  OutputComp::X(x) => f.get(x).unwrap_or(&Vec::new()).clone(),
                })
                .collect::<Vec<_>>()
            })
          })
          .collect::<HashSet<_>>()
          .into_iter()
          .collect()
      },
    )
  }

  pub fn variables(&self) -> &HashSet<V> {
    &self.variables
  }
}
impl<D, S, V> SymSST<D, Predicate<D>, FunctionTermImpl<D>, S, V>
where
  D: Domain,
  S: State,
  V: Variable,
{
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
      variables: v1,
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

    let cartesian = s1
      .into_iter()
      .flat_map(|p| {
        s2.iter()
          .map(move |q| ((S::clone(&p), S::clone(q)), S::new()))
      })
      .collect::<HashMap<_, _>>();

    let initial_state = cartesian.get(&(i1, i2)).expect(error_msg).clone();

    let mut variables = v1.into_iter().chain(v2.into_iter()).collect::<HashSet<_>>();
    variables.insert(V::clone(result));

    let mut output_function = HashMap::new();
    let mut transition: Transition<Predicate<D>, FunctionTermImpl<D>, S, V> = t1
      .iter()
      .flat_map(|((p1, phi1), v1)| {
        t2.iter()
          .map(|((p2, phi2), v2)| {
            let p = S::clone(
              cartesian
                .get(&(S::clone(p1), S::clone(p2)))
                .expect(error_msg),
            );
            let v = v1
              .into_iter()
              .flat_map(|(q1, u1)| {
                v2.into_iter()
                  .map(|(q2, u2)| {
                    let q = S::clone(
                      cartesian
                        .get(&(S::clone(q1), S::clone(q2)))
                        .expect(error_msg),
                    );

                    let u = u1
                      .iter()
                      .chain(u2.into_iter())
                      .map(|(v, uc)| (V::clone(&v), uc.clone()))
                      .collect::<HashMap<_, _>>();

                    (q, u)
                  })
                  .collect::<Vec<_>>()
              })
              .collect();

            ((p, phi1.and(phi2)), v)
          })
          .collect::<Vec<_>>()
      })
      .collect();

    for (fs1, o1) in o1.iter() {
      for (fs2, o2) in o2.iter() {
        let fs = cartesian
          .get(&(S::clone(fs1), S::clone(fs2)))
          .expect(error_msg);

        output_function.insert(S::clone(fs), o1.clone());

        if let Some(target) = transition.get_mut(&(S::clone(fs), Predicate::char(D::separator()))) {
          for (_, update) in target {
            update.insert(
              V::clone(result),
              o2.into_iter()
                .map(|out| match out {
                  OutputComp::A(a) => UpdateComp::F(Lambda::constant(D::clone(a))),
                  OutputComp::X(var) => UpdateComp::X(V::clone(var)),
                })
                .collect(),
            );
          }
        } else {
          transition.insert(
            (S::clone(fs), Predicate::char(D::separator())),
            vec![(
              S::clone(fs),
              HashMap::from([(
                V::clone(result),
                o2.into_iter()
                  .map(|out| match out {
                    OutputComp::A(a) => UpdateComp::F(Lambda::constant(D::clone(a))),
                    OutputComp::X(var) => UpdateComp::X(V::clone(var)),
                  })
                  .collect(),
              )]),
            )],
          );
        }
      }
    }

    let states = cartesian.into_values().collect();

    Sst::new(
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
    let SymSST {
      states: s1,
      variables: v1,
      initial_state,
      output_function: o1,
      transition: t1,
    } = self;

    let SymSST {
      states: s2,
      variables: v2,
      initial_state: i2,
      output_function: o2,
      transition: t2,
    } = other;

    let states = s1.into_iter().chain(s2.into_iter()).collect();

    let mut variables = v1.into_iter().chain(v2.into_iter()).collect::<HashSet<_>>();
    let res_of_self = V::new();

    let mut res_vars = HashSet::new();
    res_vars.insert(V::clone(&res_of_self));
    for (fs1, _) in o1.iter() {
      if let Some(target) = t1.get(&(S::clone(fs1), Predicate::char(D::separator()))) {
        for (_, u) in target {
          for var in u.keys() {
            res_vars.insert(V::clone(var));
          }
        }
      }
    }

    let joint = o1.into_iter().map(|(fs1, out)| {
      let joint;
      if let Some(target) = t1.get(&(S::clone(&fs1), Predicate::char(D::separator()))) {
        joint = target
          .iter()
          .map(|(_, u)| {
            let mut u = u.clone();
            u.insert(
              V::clone(&res_of_self),
              out
                .iter()
                .map(|oc| match oc {
                  OutputComp::A(a) => UpdateComp::F(Lambda::constant(D::clone(a))),
                  OutputComp::X(var) => UpdateComp::X(V::clone(var)),
                })
                .collect(),
            );
            (S::clone(&i2), u)
          })
          .collect();
      } else {
        joint = vec![(
          S::clone(&i2),
          HashMap::from([(
            V::clone(&res_of_self),
            out
              .into_iter()
              .map(|oc| match oc {
                OutputComp::A(a) => UpdateComp::F(Lambda::constant(a)),
                OutputComp::X(var) => UpdateComp::X(var),
              })
              .collect(),
          )]),
        )]
      }

      ((fs1, Predicate::char(D::separator())), joint)
    });

    let extend_transition = |((p, phi), target): (
      Source<Predicate<D>, S>,
      Vec<Target<FunctionTermImpl<D>, S, V>>,
    )| {
      (
        (p, phi),
        target
          .into_iter()
          .map(|(q, mut u)| {
            res_vars.iter().for_each(|var| {
              u.insert(V::clone(&var), vec![UpdateComp::X(V::clone(&var))]);
            });
            (q, u)
          })
          .collect(),
      )
    };

    let transition = t2
      .into_iter()
      .map(extend_transition)
      .chain(t1.iter().map(|(src, trg)| (src.clone(), trg.clone())))
      .chain(joint)
      .collect();

    let output_function = o2
      .into_iter()
      .map(|(fs, out)| {
        (
          fs,
          [
            OutputComp::X(V::clone(&res_of_self)),
            OutputComp::A(D::separator()),
          ]
          .iter()  //https://doc.rust-lang.org/nightly/edition-guide/rust-2021/IntoIterator-for-arrays.html
          .cloned()
          .chain(out.into_iter())
          .collect(),
        )
      })
      .collect();

    variables.insert(res_of_self);

    SymSST::new(
      states,
      variables,
      initial_state,
      output_function,
      transition,
    )
  }
}
impl<D, B, F, S, V> StateMachine for SymSST<D, B, F, S, V>
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
      transition: HashMap::new(),
    }
  }

  state::macros::impl_state_machine!(states, initial_state, output_function, transition);
}

pub type Sst<T, S, V> = SymSST<T, Predicate<T>, FunctionTermImpl<T>, S, V>;
