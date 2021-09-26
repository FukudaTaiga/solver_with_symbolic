#![allow(dead_code)]
use super::recognizable::Recognizable;
use crate::boolean_algebra::BoolAlg;
use crate::state::{State, StateMachine};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;

/**
 * symbolic automata
 */
#[derive(Debug)]
pub struct SymFA<T: BoolAlg + Eq + Hash> {
    pub states: HashSet<Rc<State>>,
    pub initial_state: Rc<State>,
    pub final_states: HashSet<Rc<State>>,
    pub transition: HashMap<(Rc<State>, Rc<T>), Rc<State>>,
}
impl<T: BoolAlg + Eq + Hash> SymFA<T> {
    pub fn new(
        states: HashSet<Rc<State>>,
        initial_state: Rc<State>,
        final_states: HashSet<Rc<State>>,
        transition: HashMap<(Rc<State>, Rc<T>), Rc<State>>,
    ) -> SymFA<T> {
        let mut sfa = SymFA {
            states,
            initial_state,
            final_states,
            transition,
        };
        sfa.minimize();
        sfa
    }

    fn state_predicate<'a>(&self, q: State) -> RefCell<Rc<T>> {
        let result = RefCell::new(Rc::new(T::top()));
        for (s, phi) in self.transition.keys() {
            if **s == q {
                *result.borrow_mut() = Rc::new(T::or(&Rc::clone(&result.borrow()), &Rc::clone(phi)))
            }
        }

        return result;
    }

    pub fn concat(self, other: SymFA<T>) -> SymFA<T> {
        let SymFA {
            states: s1,
            initial_state,
            final_states: f1,
            transition: t1,
        } = self;
        let SymFA {
            states: s2,
            initial_state: i2,
            final_states: f2,
            transition: t2,
        } = other;

        let states = s1.into_iter().chain(s2.into_iter()).collect::<HashSet<_>>();
        let final_states = if f2.contains(&i2) {
            f2.into_iter()
                .chain(f1.iter().map(|final_state| Rc::clone(final_state)))
                .collect()
        } else {
            f2
        };
        let transition = t1
            .into_iter()
            .chain(t2.into_iter().flat_map(|((state2, phi2), next2)| {
                if state2 == i2 {
                    f1.iter()
                        .map(|final_state| {
                            (
                                (Rc::clone(final_state), Rc::clone(&phi2)),
                                Rc::clone(&next2),
                            )
                        })
                        .chain(vec![(
                            (Rc::clone(&state2), Rc::clone(&phi2)),
                            Rc::clone(&next2),
                        )])
                        .collect()
                } else {
                    vec![((Rc::clone(&state2), Rc::clone(&phi2)), Rc::clone(&next2))]
                }
            }))
            .collect::<HashMap<_, _>>();

        SymFA::new(states, initial_state, final_states, transition)
    }

    pub fn or(self, other: SymFA<T>) -> SymFA<T> {
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

        let initial_state = Rc::new(State::new());
        let states = s1
            .into_iter()
            .chain(s2.into_iter())
            .chain(vec![Rc::clone(&initial_state)].into_iter())
            .collect::<HashSet<_>>();
        let final_states = f1.into_iter().chain(f2.into_iter()).collect::<HashSet<_>>();
        let transition = t1
            .into_iter()
            .flat_map(|((state, phi), next)| {
                if state == i1 {
                    vec![
                        ((Rc::clone(&state), Rc::clone(&phi)), Rc::clone(&next)),
                        (
                            (Rc::clone(&initial_state), Rc::clone(&phi)),
                            Rc::clone(&next),
                        ),
                    ]
                } else {
                    vec![((Rc::clone(&state), Rc::clone(&phi)), Rc::clone(&next))]
                }
            })
            .chain(t2.into_iter().flat_map(|((state, phi), next)| {
                if state == i2 {
                    vec![
                        ((Rc::clone(&state), Rc::clone(&phi)), Rc::clone(&next)),
                        (
                            (Rc::clone(&initial_state), Rc::clone(&phi)),
                            Rc::clone(&next),
                        ),
                    ]
                } else {
                    vec![((Rc::clone(&state), Rc::clone(&phi)), Rc::clone(&next))]
                }
            }))
            .collect::<HashMap<_, _>>();

        SymFA::new(states, initial_state, final_states, transition)
    }

    pub fn not(self) -> SymFA<T> {
        let SymFA {
            states,
            initial_state,
            final_states: f,
            transition,
        } = self;

        let final_states = &states - &f;

        SymFA::new(states, initial_state, final_states, transition)
    }

    pub fn star(self) -> SymFA<T> {
        let SymFA {
            states: s,
            initial_state: i,
            final_states: f,
            transition: t,
        } = self;

        let initial_state = Rc::new(State::new());

        let states = s
            .iter()
            .map(|state| Rc::clone(state))
            .chain([Rc::clone(&initial_state)])
            .collect();

        let final_states = f
            .iter()
            .map(|final_state| Rc::clone(final_state))
            .chain([Rc::clone(&initial_state)])
            .collect();

        let transition = t
            .into_iter()
            .flat_map(|((state, phi), next)| {
                if state == i {
                    f.iter()
                        .map(|final_state| {
                            ((Rc::clone(final_state), Rc::clone(&phi)), Rc::clone(&next))
                        })
                        .chain(vec![
                            ((Rc::clone(&state), Rc::clone(&phi)), Rc::clone(&next)),
                            (
                                (Rc::clone(&initial_state), Rc::clone(&phi)),
                                Rc::clone(&next),
                            ),
                        ])
                        .collect()
                } else {
                    vec![((Rc::clone(&state), Rc::clone(&phi)), Rc::clone(&next))]
                }
            })
            .collect();

        SymFA::new(states, initial_state, final_states, transition)
    }
}
impl<T: BoolAlg + Eq + Hash> Recognizable<T::Domain> for SymFA<T> {
    fn run(&self, input: &[T::Domain]) -> bool {
        let mut current_states = HashSet::new();
        current_states.insert(Rc::clone(&self.initial_state));

        for a in input {
            current_states = current_states
                .into_iter()
                .flat_map(|current_state| {
                    self.transition
                        .iter()
                        .filter_map(|((state, phi), next)| {
                            if *state == current_state && phi.denotate(a) {
                                Some(Rc::clone(next))
                            } else {
                                None
                            }
                        })
                        .collect::<HashSet<_>>()
                })
                .collect::<HashSet<_>>();
        }

        !&current_states.is_disjoint(&self.final_states)
    }
}
impl<T: BoolAlg + Eq + Hash> StateMachine for SymFA<T> {
    type Source = (Rc<State>, Rc<T>);
    type Target = Rc<State>;
    type FinalSet = HashSet<Rc<State>>;

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
        &self.final_states
    }
    fn final_set_mut(&mut self) -> &mut Self::FinalSet {
        &mut self.final_states
    }
    fn final_set_filter_by_states(&self, reachables: &HashSet<Rc<State>>) -> Self::FinalSet {
        self.final_states
            .intersection(reachables)
            .map(|final_state| Rc::clone(final_state))
            .collect()
    }

    fn source_to_state(s: &Self::Source) -> &Rc<State> {
        &s.0
    }
    fn target_to_state(t: &Self::Target) -> &Rc<State> {
        t
    }
    fn clone_source(s: &Self::Source) -> Self::Source {
        (Rc::clone(&s.0), Rc::clone(&s.1))
    }
    fn clone_target(t: &Self::Target) -> Self::Target {
        Rc::clone(t)
    }

    fn transition(&self) -> &HashMap<Self::Source, Self::Target> {
        &self.transition
    }
    fn transition_mut(&mut self) -> &mut HashMap<Self::Source, Self::Target> {
        &mut self.transition
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boolean_algebra::Predicate;

    #[test]
    fn create_sfa_without_new() {
        let mut states = HashSet::new();
        let mut final_states = HashSet::new();
        let mut transition = HashMap::new();

        let initial_state = Rc::new(State::new());
        states.insert(Rc::clone(&initial_state));

        let rebundon_state = Rc::new(State::new());
        states.insert(Rc::clone(&rebundon_state));

        let final_state = Rc::new(State::new());
        states.insert(Rc::clone(&final_state));
        final_states.insert(Rc::clone(&final_state));

        let abc = Rc::new(Predicate::range(Some('a'), Some('d')).unwrap());
        let not_abc = Rc::new(Predicate::not(&abc));
        transition.insert(
            (Rc::clone(&initial_state), Rc::clone(&abc)),
            Rc::clone(&final_state),
        );
        transition.insert(
            (Rc::clone(&initial_state), Rc::clone(&not_abc)),
            Rc::clone(&initial_state),
        );

        let w = Rc::new(Predicate::eq('w'));
        let not_w = Rc::new(Predicate::not(&w));
        transition.insert(
            (Rc::clone(&final_state), Rc::clone(&w)),
            Rc::clone(&initial_state),
        );
        transition.insert(
            (Rc::clone(&final_state), Rc::clone(&not_w)),
            Rc::clone(&final_state),
        );

        let sym_fa = SymFA {
            states,
            initial_state,
            final_states,
            transition,
        };

        println!("{:#?}", sym_fa);
        assert_eq!(sym_fa.states.len(), 3);
        assert!(sym_fa.run(&"afvfdl".chars().collect::<Vec<char>>()[..]));
        assert!(!sym_fa.run(&"".chars().collect::<Vec<char>>()[..]));
        assert!(sym_fa.run(&"awa".chars().collect::<Vec<char>>()[..]));
        assert!(sym_fa.run(&"cwbwad".chars().collect::<Vec<char>>()[..]));
        assert!(!sym_fa.run(&"cwbwadww".chars().collect::<Vec<char>>()[..]));
    }

    #[test]
    fn create_sfa_with_new() {
        let mut states = HashSet::new();
        let mut final_states = HashSet::new();
        let mut transition = HashMap::new();

        let initial_state = Rc::new(State::new());
        states.insert(Rc::clone(&initial_state));

        let rebundon_state = Rc::new(State::new());
        states.insert(Rc::clone(&rebundon_state));

        let final_state = Rc::new(State::new());
        states.insert(Rc::clone(&final_state));
        final_states.insert(Rc::clone(&final_state));

        let abc = Rc::new(Predicate::range(Some('a'), Some('d')).unwrap());
        let not_abc = Rc::new(Predicate::not(&abc));
        transition.insert(
            (Rc::clone(&initial_state), Rc::clone(&abc)),
            Rc::clone(&final_state),
        );
        transition.insert(
            (Rc::clone(&initial_state), Rc::clone(&not_abc)),
            Rc::clone(&initial_state),
        );

        let w = Rc::new(Predicate::eq('w'));
        let not_w = Rc::new(Predicate::not(&w));
        transition.insert(
            (Rc::clone(&final_state), Rc::clone(&w)),
            Rc::clone(&initial_state),
        );
        transition.insert(
            (Rc::clone(&final_state), Rc::clone(&not_w)),
            Rc::clone(&final_state),
        );

        let sym_fa = SymFA::new(states, initial_state, final_states, transition);
        println!("{:#?}", sym_fa);
        assert_eq!(sym_fa.states.len(), 2);
        assert!(sym_fa.run(&"afvfdl".chars().collect::<Vec<char>>()[..]));
        assert!(!sym_fa.run(&"".chars().collect::<Vec<char>>()[..]));
        assert!(sym_fa.run(&"awa".chars().collect::<Vec<char>>()[..]));
        assert!(sym_fa.run(&"cwbwad".chars().collect::<Vec<char>>()[..]));
        assert!(!sym_fa.run(&"cwbwadww".chars().collect::<Vec<char>>()[..]));
    }
}
