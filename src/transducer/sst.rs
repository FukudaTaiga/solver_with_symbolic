#![allow(dead_code)]
use super::term::*;
use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::state::{State, StateMachine};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;

/**
 * implementation of symbolic streaming string transducer (SSST)
 */
pub struct SymSST<'a, S: FunctionTerm> {
    states: HashSet<Rc<State>>,
    variables: HashSet<Rc<Variable<'a>>>,
    initial_state: Rc<State>,
    output_function:
        HashMap<Rc<State>, Rc<Vec<OutputComp<'a, <S::Underlying as BoolAlg>::Domain>>>>,
    pub transition: HashMap<
        (Rc<State>, Rc<S::Underlying>),
        (
            Rc<State>,
            HashMap<Rc<Variable<'a>>, Rc<Vec<UpdateComp<'a, S>>>>,
        ),
    >,
}
impl<'a, S: FunctionTerm> SymSST<'a, S> {
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
                    self.transition
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
                                                        UpdateComp::X(y) => alpha
                                                            .get(y)
                                                            .unwrap_or(&Vec::new())
                                                            .clone(),
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
impl<'a, T: PartialOrd + Copy + Eq + Hash> SymSST<'a, Lambda<Predicate<'a, T>>> {
    pub fn new(
        states: HashSet<Rc<State>>,
        variables: HashSet<Rc<Variable<'a>>>,
        initial_state: Rc<State>,
        output_function: HashMap<Rc<State>, Rc<Vec<OutputComp<'a, T>>>>,
        transition: HashMap<
            (Rc<State>, Rc<Predicate<'a, T>>),
            (
                Rc<State>,
                HashMap<Rc<Variable<'a>>, Rc<Vec<UpdateComp<'a, Lambda<Predicate<'a, T>>>>>>,
            ),
        >,
    ) -> SymSST<'a, Lambda<Predicate<'a, T>>> {
        let mut ssst = Self {
            states,
            variables,
            initial_state,
            output_function,
            transition,
        };
        ssst.minimize();
        ssst
    }
}
impl<'a, T: PartialOrd + Copy + Eq + Hash> StateMachine for SymSST<'a, Lambda<Predicate<'a, T>>> {
    type Source = (Rc<State>, Rc<Predicate<'a, T>>);
    type Target = (
        Rc<State>,
        HashMap<Rc<Variable<'a>>, Rc<Vec<UpdateComp<'a, Lambda<Predicate<'a, T>>>>>>,
    );
    type FinalSet = HashMap<Rc<State>, Rc<Vec<OutputComp<'a, T>>>>;

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
        self.output_function
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
    fn clone_source(s: &Self::Source) -> Self::Source {
        (Rc::clone(&s.0), Rc::clone(&s.1))
    }
    fn clone_target(t: &Self::Target) -> Self::Target {
        (
            Rc::clone(&t.0),
            t.1.iter()
                .map(|(x, alpha_x)| (Rc::clone(x), Rc::clone(alpha_x)))
                .collect(),
        )
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
        (
            Rc<State>,
            HashMap<Rc<Variable<'a>>, Rc<Vec<UpdateComp<'a, S>>>>,
        ),
    >,
    iter: std::slice::Iter<<<S as FunctionTerm>::Underlying as BoolAlg>::Domain>,
    possibilities: Vec<(
        Rc<State>,
        HashMap<Rc<Variable<'a>>, Vec<<<S as FunctionTerm>::Underlying as BoolAlg>::Domain>>,
    )>,
) -> Vec<(
    Rc<State>,
    HashMap<Rc<Variable<'a>>, Vec<<<S as FunctionTerm>::Underlying as BoolAlg>::Domain>>,
)>
where
    <S::Underlying as BoolAlg>::Domain: Copy,
{
    let mut iter = iter;
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
                                                UpdateComp::X(y) => {
                                                    alpha.get(y).unwrap_or(&Vec::new()).clone()
                                                }
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
