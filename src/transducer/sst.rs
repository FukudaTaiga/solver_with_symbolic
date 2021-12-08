use super::term::{FunctionTerm, FunctionTermImpl, Lambda, OutputComp, UpdateComp, VariableImpl};
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::char_util::FromChar;
use crate::state::{StateImpl, StateMachine};
use std::{
  collections::{HashMap, HashSet},
  fmt::Debug,
  rc::Rc,
};

type Domain<F> = <<F as FunctionTerm>::Underlying as BoolAlg>::Domain;
type UpdateFunction<F, V> = HashMap<V, Vec<UpdateComp<F, V>>>;
type Source<F, S> = (S, Rc<<F as FunctionTerm>::Underlying>);
type Target<F, S, V> = (S, UpdateFunction<F, V>);
type Output<F, V> = Vec<OutputComp<Domain<F>, V>>;

/** implementation of symbolic streaming string transducer (SSST) */
#[derive(Debug, PartialEq, Clone)]
pub struct SymSST<F, S, V>
where
  F: FunctionTerm,
  S: StateImpl,
  V: VariableImpl,
{
  pub(crate) states: HashSet<S>,
  pub(crate) variables: HashSet<V>,
  pub(crate) initial_state: S,
  pub(crate) output_function: HashMap<S, Output<F, V>>,
  pub(crate) transition: HashMap<Source<F, S>, Target<F, S, V>>,
}
impl<F, S, V> SymSST<F, S, V>
where
  F: FunctionTerm + Clone,
  S: StateImpl,
  V: VariableImpl,
{
  pub(crate) fn empty() -> Self {
    let state = S::new();
    Self::new(
      HashSet::from([S::clone(&state)]),
      HashSet::new(),
      S::clone(&state),
      HashMap::from([(state, vec![])]),
      HashMap::new(),
    )
  }

  pub fn new(
    states: HashSet<S>,
    variables: HashSet<V>,
    initial_state: S,
    output_function: HashMap<S, Output<F, V>>,
    transition: HashMap<Source<F, S>, Target<F, S, V>>,
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
  pub fn run(&self, input: &[Domain<F>]) -> Vec<Vec<Domain<F>>> {
    let mut input = input.iter();
    let mut possibilities = vec![];
    let map = self
      .variables
      .iter()
      .map(|var| (V::clone(var), vec![]))
      .collect::<HashMap<_, _>>();
    let state = self.initial_state.clone();
    possibilities.push((state, map));

    while let Some(c) = input.next() {
      // eprintln!("char: {:?}", c);
      // eprintln!("possibilities: {:?}", possibilities);
      possibilities = possibilities
        .into_iter()
        .flat_map(|(state, map)| {
          self
            .transition
            .iter()
            .filter_map(move |((p, phi), (q, alpha))| {
              if *p == state && phi.denotate(c) {
                Some((
                  S::clone(q),
                  self
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
                            UpdateComp::F(f) => vec![Domain::<F>::clone(f.apply(c))],
                            UpdateComp::X(var) => map.get(var).unwrap_or(&vec![]).clone(),
                          })
                          .collect(),
                      )
                    })
                    .collect(),
                ))
              } else {
                None
              }
            })
            .collect::<HashMap<_, _>>()
        })
        .collect()
    }

    possibilities
      .into_iter()
      .filter_map(|(q, f)| {
        self.output_function.get(&q).map(|w| {
          w.iter()
            .flat_map(|o| match o {
              OutputComp::A(a) => vec![Domain::<F>::clone(a)],
              OutputComp::X(x) => f.get(&*x).unwrap_or(&Vec::new()).clone(),
            })
            .collect::<Vec<_>>()
        })
      })
      .collect()
  }

  /**
   * merging two transition and variables,
   * Note, it is not a composition nor concatenation.
   * only for used to making normalized ssst in my theory.
   */
  pub(crate) fn merge(self, other: Self) -> Self {
    let error_msg = "Uncontrolled states exist. this will happen for developper's error";

    let SymSST {
      states: s1,
      variables: v1,
      initial_state: i1,
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

    let cartesian = s1
      .iter()
      .flat_map(|p| s2.iter().map(move |q| ((p.clone(), q.clone()), S::new())))
      .collect::<HashMap<_, _>>();

    let initial_state = cartesian.get(&(i1, i2)).expect(error_msg).clone();

    let variables = v1.into_iter().chain(v2.into_iter()).collect();

    let output_function = o1
      .iter()
      .flat_map(|(fs1, o1)| {
        o2.iter()
          .map(|(fs2, o2)| {
            (
              cartesian
                .get(&(S::clone(fs1), S::clone(fs2)))
                .expect(error_msg)
                .clone(),
              o1.iter().chain(o2.iter()).map(|oc| oc.clone()).collect(),
            )
          })
          .collect::<Vec<_>>()
      })
      .collect();

    let transition = t1
      .iter()
      .flat_map(|((p1, phi1), (q1, u1))| {
        t2.iter()
          .map(|((p2, phi2), (q2, u2))| {
            let p = cartesian
              .get(&(S::clone(p1), S::clone(p2)))
              .expect(error_msg)
              .clone();
            let q = cartesian
              .get(&(S::clone(q1), S::clone(q2)))
              .expect(error_msg)
              .clone();

            (
              (p, phi1.and(phi2)),
              (
                q,
                u1.iter()
                  .chain(u2.iter())
                  .map(|(v, uc)| (v.clone(), uc.clone()))
                  .collect(),
              ),
            )
          })
          .collect::<Vec<_>>()
      })
      .collect();

    let states = cartesian.into_values().collect();

    SymSST::new(
      states,
      variables,
      initial_state,
      output_function,
      transition,
    )
  }

  pub fn variables(&self) -> &HashSet<V> {
    &self.variables
  }
}
impl<T, S, V> SymSST<FunctionTermImpl<T>, S, V>
where
  T: FromChar,
  S: StateImpl,
  V: VariableImpl,
{
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
      if let Some((_, u)) = t1.get(&(S::clone(fs1), Predicate::eq(T::separator()))) {
        for var in u.keys() {
          res_vars.insert(V::clone(var));
        }
      }
    }

    let joint = o1.into_iter().map(|(fs1, out)| {
      let mut step_to_other = t1
        .get(&(S::clone(&fs1), Predicate::eq(T::separator())))
        .map(|(_, u)| u.clone())
        .unwrap_or(HashMap::new());
      step_to_other.insert(
        V::clone(&res_of_self),
        out
          .into_iter()
          .map(|oc| match oc {
            OutputComp::A(a) => UpdateComp::F(Lambda::constant(a)),
            OutputComp::X(var) => UpdateComp::X(var),
          })
          .collect(),
      );
      (
        (fs1, Predicate::eq(T::separator())),
        (S::clone(&i2), step_to_other),
      )
    });

    let extend_transition = |((p, phi), (q, mut u)): (
      (S, Rc<Predicate<T>>),
      (S, UpdateFunction<FunctionTermImpl<T>, V>),
    )| {
      for var in res_vars.iter() {
        u.insert(V::clone(&var), vec![UpdateComp::X(V::clone(&var))]);
      }

      ((p, phi), (q, u))
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
          vec![
            OutputComp::X(V::clone(&res_of_self)),
            OutputComp::A(T::separator()),
          ]
          .into_iter()
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
impl<F, S, V> StateMachine for SymSST<F, S, V>
where
  F: FunctionTerm + Clone,
  S: StateImpl,
  V: VariableImpl,
{
  type StateType = S;

  type Source = Source<F, S>;
  type Target = Target<F, S, V>;
  type FinalSet = HashMap<S, Output<F, V>>;

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
    &self.output_function
  }
  fn final_set_mut(&mut self) -> &mut Self::FinalSet {
    &mut self.output_function
  }
  fn final_set_filter_by_states<U: FnMut(&Self::StateType) -> bool>(
    &self,
    mut filter: U,
  ) -> Self::FinalSet {
    self
      .output_function
      .iter()
      .filter_map(|(state, out)| {
        if filter(state) {
          Some((S::clone(state), out.clone()))
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
    &t.0
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

pub type Sst<T, S, V> = SymSST<FunctionTermImpl<T>, S, V>;
