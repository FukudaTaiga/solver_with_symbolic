use super::term::*;
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::state::{State, StateMachine};
use std::{
  collections::{HashMap, HashSet},
  hash::Hash,
  rc::Rc,
};

/**
 * implementation of symbolic streaming string transducer (SSST)
 */
#[derive(Debug, PartialEq)]
pub struct SymSST<S: FunctionTerm> {
  states: HashSet<Rc<State>>,
  variables: HashSet<Rc<Variable>>,
  initial_state: Rc<State>,
  output_function: HashMap<Rc<State>, Rc<Vec<OutputComp<<S::Underlying as BoolAlg>::Domain>>>>,
  transition: HashMap<
    (Rc<State>, Rc<S::Underlying>),
    (Rc<State>, HashMap<Rc<Variable>, Rc<Vec<UpdateComp<S>>>>),
  >,
}
impl<'a, S: FunctionTerm> SymSST<S> {
  pub fn run(
    &self,
    input: &[<S::Underlying as BoolAlg>::Domain],
  ) -> Vec<Vec<<S::Underlying as BoolAlg>::Domain>>
  where
    <S::Underlying as BoolAlg>::Domain: Copy,
  {
    let mut input = input.iter();
    let mut possibilities = vec![];
    let current_map = HashMap::new();
    let current_state = Rc::clone(&self.initial_state);
    possibilities.push((current_state, current_map));

    while let Some(c) = input.next() {
      possibilities = possibilities
        .iter()
        .flat_map(|(state, alpha)| {
          self
            .transition
            .iter()
            .filter_map(move |((s1, phi), (s2, m))| {
              if **s1 == **state && phi.denotate(c) {
                Some((
                  Rc::clone(s2),
                  m.iter()
                    .map(|(x, w)| {
                      (
                        Rc::clone(x),
                        w.iter()
                          .flat_map(|u| match u {
                            UpdateComp::F(lambda) => {
                              vec![*lambda.apply(c)]
                            }
                            UpdateComp::X(y) => alpha.get(y).unwrap_or(&Vec::new()).clone(),
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
        })
        .collect()
    }

    possibilities
      .into_iter()
      .filter_map(|(q, f)| {
        self.output_function.get(&q).map(|w| {
          w.iter()
            .flat_map(|o| match o {
              OutputComp::A(a) => vec![*a],
              OutputComp::X(x) => f.get(&*x).unwrap_or(&Vec::new()).clone(),
            })
            .collect::<Vec<_>>()
        })
      })
      .collect()
  }
}
impl<'a, T> SymSST<Lambda<Predicate<T>>>
where
  T: PartialOrd + Ord + Copy + PartialEq + Eq + Hash + std::fmt::Debug,
{
  pub fn new(
    states: HashSet<Rc<State>>,
    variables: HashSet<Rc<Variable>>,
    initial_state: Rc<State>,
    output_function: HashMap<Rc<State>, Rc<Vec<OutputComp<T>>>>,
    transition: HashMap<
      (Rc<State>, Rc<Predicate<T>>),
      (
        Rc<State>,
        HashMap<Rc<Variable>, Rc<Vec<UpdateComp<Lambda<Predicate<T>>>>>>,
      ),
    >,
  ) -> SymSST<Lambda<Predicate<T>>> {
    SymSST {
      states,
      variables,
      initial_state,
      output_function,
      transition,
    }
    .minimize()
  }
}
impl<'a, T> StateMachine for SymSST<Lambda<Predicate<T>>>
where
  T: PartialOrd + Ord + Copy + PartialEq + Eq + Hash + std::fmt::Debug,
{
  type Source = (Rc<State>, Rc<Predicate<T>>);
  type Target = (
    Rc<State>,
    HashMap<Rc<Variable>, Rc<Vec<UpdateComp<Lambda<Predicate<T>>>>>>,
  );
  type FinalSet = HashMap<Rc<State>, Rc<Vec<OutputComp<T>>>>;

  fn states(&self) -> &HashSet<Rc<State>> {
    &self.states
  }
  fn states_mut(&mut self) -> &mut HashSet<Rc<State>> {
    &mut self.states
  }

  fn initial_state(&self) -> &Rc<State> {
    &self.initial_state
  }
  fn initial_state_mut(&mut self) -> &mut Rc<State> {
    &mut self.initial_state
  }

  fn final_set(&self) -> &Self::FinalSet {
    &self.output_function
  }
  fn final_set_mut(&mut self) -> &mut Self::FinalSet {
    &mut self.output_function
  }
  fn final_set_filter_by_states(&self, reachables: &HashSet<Rc<State>>) -> Self::FinalSet {
    self
      .output_function
      .iter()
      .filter_map(|(state, out)| {
        if reachables.contains(state) {
          Some((Rc::clone(state), Rc::clone(out)))
        } else {
          None
        }
      })
      .collect()
  }

  fn source_to_state(s: &Self::Source) -> &Rc<State> {
    &s.0
  }
  fn target_to_state(t: &Self::Target) -> &Rc<State> {
    &t.0
  }

  fn transition(&self) -> &HashMap<Self::Source, Self::Target> {
    &self.transition
  }
  fn transition_mut(&mut self) -> &mut HashMap<Self::Source, Self::Target> {
    &mut self.transition
  }
}

//for refactering
fn __inner_run<'a, S: FunctionTerm>(
  transition: HashMap<
    (Rc<State>, Rc<S::Underlying>),
    (Rc<State>, HashMap<Rc<Variable>, Rc<Vec<UpdateComp<S>>>>),
  >,
  mut iter: std::slice::Iter<<<S as FunctionTerm>::Underlying as BoolAlg>::Domain>,
  possibilities: Vec<(
    Rc<State>,
    HashMap<Rc<Variable>, Vec<<<S as FunctionTerm>::Underlying as BoolAlg>::Domain>>,
  )>,
) -> Vec<(
  Rc<State>,
  HashMap<Rc<Variable>, Vec<<<S as FunctionTerm>::Underlying as BoolAlg>::Domain>>,
)>
where
  <S::Underlying as BoolAlg>::Domain: Copy,
{
  if let Some(c) = iter.next() {
    let next = possibilities
      .iter()
      .flat_map(|(state, alpha)| {
        transition.iter().filter_map(move |((s1, phi), (s2, m))| {
          if **s1 == **state && phi.denotate(c) {
            Some((
              Rc::clone(s2),
              m.iter()
                .map(|(x, w)| {
                  (
                    Rc::clone(x),
                    w.iter()
                      .flat_map(|u| match u {
                        UpdateComp::F(lambda) => {
                          vec![*lambda.apply(c)]
                        }
                        UpdateComp::X(y) => alpha.get(y).unwrap_or(&Vec::new()).clone(),
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
      })
      .collect();
    __inner_run(transition, iter, next)
  } else {
    possibilities
  }
}

pub type SST<T> = SymSST<Lambda<Predicate<T>>>;
