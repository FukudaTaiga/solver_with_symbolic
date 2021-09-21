#![allow(dead_code)]
use super::recognizable::Recognizable;
use super::symbolic_automata::*;
use crate::boolean_algebra::{BoolAlg, Predicate};
use std::cmp::PartialOrd;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::rc::Rc;

//Errors
const NO_INPUT: &str = "Parse Error: No lefthand input found";
//const OPERATOR_EXPECTED: &str = "Parse Error: Operator Expected";
const NOT_ENOUGH_ARGUMENT: &str = "Parse Error:  Not enough argument of some operator";
const INVALID_OPERATION: &str = "Unreachable: Invalid operation";
const NO_MATCHING_BRA: &str = "Parse Error: No matching bracket '(' found";
const NO_MATCHING_CKET: &str = "Parse Error: No matching bracket ')' found";
const UNNECESSARY_BRACKET: &str = "Parse Error: Unnecessary brackets found";

//should use Rc
#[derive(Debug, PartialEq)]
pub enum Regex<T: PartialOrd> {
  Empty,
  Epsilon,
  All,
  Element(T),
  Range(Option<T>, Option<T>),
  Concat(Box<Regex<T>>, Box<Regex<T>>),
  Or(Box<Regex<T>>, Box<Regex<T>>),
  Star(Box<Regex<T>>),
  Not(Box<Regex<T>>),
}
impl<T: PartialOrd + Copy + Eq + Hash> Regex<T> {
  /**
   * identifier must be '!' or '_' \
   * map them Empty and All
   */
  fn to_regex(identifier: char) -> Regex<T> {
    match identifier {
      '!' => Regex::Empty,
      '_' => Regex::All,
      _ => unreachable!(),
    }
  }

  /**
   * apply operator to self, if binary operator, and other \
   * possible errors: INVALID_OPERATION
   */
  fn apply(self, op: char, other: Option<Regex<T>>) -> Result<Regex<T>, &'static str> {
    match op {
      '#' => other
        .ok_or(INVALID_OPERATION)
        .map(|r| Regex::Concat(Box::new(self), Box::new(r))),
      '|' => other
        .ok_or(INVALID_OPERATION)
        .map(|r| Regex::Or(Box::new(self), Box::new(r))),
      '*' => Ok(Regex::Star(Box::new(self))),
      '~' => Ok(Regex::Not(Box::new(self))),
      '!' => Ok(Regex::Concat(Box::new(self), Box::new(Regex::Empty))),
      '_' => Ok(Regex::Concat(Box::new(self), Box::new(Regex::All))),
      _ => Err(INVALID_OPERATION),
    }
  }

  fn reduce(self) -> Regex<T> {
    match self {
      Regex::Concat(r1, r2) => match (*r1, *r2) {
        (Regex::Empty, _) | (_, Regex::Empty) => Regex::Empty,
        (Regex::Epsilon, r) | (r, Regex::Epsilon) => r.reduce(),
        (left, right) => Regex::Concat(Box::new(left.reduce()), Box::new(right.reduce())),
      },
      Regex::Or(r1, r2) => match (*r1, *r2) {
        (Regex::Empty, r) | (r, Regex::Empty) => r.reduce(),
        (left, right) => Regex::Or(Box::new(left.reduce()), Box::new(right.reduce())),
      },
      Regex::Star(r) => {
        if let Regex::Empty = *r {
          Regex::Epsilon
        } else {
          Regex::Star(Box::new(r.reduce()))
        }
      }
      _ => self,
    }
  }

  pub fn to_sym_fa<'a>(&self) -> SymFA<Predicate<'a, T>> {
    match self {
      Regex::Empty => {
        let initial_state = Rc::new(State::new());
        let mut states = HashSet::new();
        let final_states = HashSet::new();
        let transition = HashMap::new();
        states.insert(Rc::clone(&initial_state));

        SymFA {
          states,
          initial_state,
          final_states,
          transition,
        }
      }
      Regex::Epsilon => {
        let initial_state = Rc::new(State::new());
        let mut states = HashSet::new();
        let mut final_states = HashSet::new();
        let mut transition = HashMap::new();
        let refusal_state = Rc::new(State::new());

        states.insert(Rc::clone(&initial_state));
        states.insert(Rc::clone(&refusal_state));

        final_states.insert(Rc::clone(&initial_state));

        transition.insert(
          (Rc::clone(&initial_state), Rc::new(Predicate::<T>::top())),
          Rc::clone(&refusal_state),
        );

        SymFA {
          states,
          initial_state,
          final_states,
          transition,
        }
      }
      Regex::Element(a) => {
        let initial_state = Rc::new(State::new());
        let mut states = HashSet::new();
        let mut final_states = HashSet::new();
        let mut transition = HashMap::new();
        let final_state = Rc::new(State::new());

        states.insert(Rc::clone(&initial_state));
        states.insert(Rc::clone(&final_state));
        final_states.insert(Rc::clone(&final_state));

        transition.insert(
          (Rc::clone(&initial_state), Rc::new(Predicate::<T>::eq(*a))),
          Rc::clone(&final_state),
        );

        SymFA {
          states,
          initial_state,
          final_states,
          transition,
        }
      }
      Regex::All => {
        let initial_state = Rc::new(State::new());
        let mut states = HashSet::new();
        let mut final_states = HashSet::new();
        let mut transition = HashMap::new();
        let final_state = Rc::new(State::new());

        states.insert(Rc::clone(&initial_state));
        states.insert(Rc::clone(&final_state));

        final_states.insert(Rc::clone(&final_state));

        transition.insert(
          (Rc::clone(&initial_state), Rc::new(Predicate::<T>::top())),
          Rc::clone(&final_state),
        );

        SymFA {
          states,
          initial_state,
          final_states,
          transition,
        }
      }
      Regex::Range(left, right) => {
        let initial_state = Rc::new(State::new());
        let mut states = HashSet::new();
        let mut final_states = HashSet::new();
        let mut transition = HashMap::new();
        let final_state = Rc::new(State::new());

        states.insert(Rc::clone(&initial_state));
        states.insert(Rc::clone(&final_state));

        final_states.insert(Rc::clone(&final_state));

        transition.insert(
          (
            Rc::clone(&initial_state),
            Rc::new(Predicate::range(*left, *right).unwrap()),
          ),
          Rc::clone(&final_state),
        );

        SymFA {
          states,
          initial_state,
          final_states,
          transition,
        }
      }
      Regex::Concat(r1, r2) => {
        let SymFA {
          states: s1,
          initial_state,
          final_states: f1,
          transition: t1,
        } = r1.to_sym_fa();
        let SymFA {
          states: s2,
          initial_state: i2,
          final_states,
          transition: t2,
        } = r2.to_sym_fa();

        let states = s1.into_iter().chain(s2.into_iter()).collect::<HashSet<_>>();
        let filtered = f1
          .iter()
          .flat_map(|final_state| {
            t2.iter()
              .filter_map(|((state2, phi2), next2)| {
                if *state2 == i2 {
                  Some(((Rc::clone(final_state), Rc::clone(phi2)), Rc::clone(next2)))
                } else {
                  None
                }
              })
              .collect::<HashMap<_, _>>()
          })
          .collect::<HashMap<_, _>>();
        let transition = t1
          .into_iter()
          .chain(t2.into_iter())
          .chain(filtered)
          .collect::<HashMap<_, _>>();

        SymFA {
          states,
          initial_state,
          final_states,
          transition,
        }
      }
      Regex::Or(r1, r2) => {
        let SymFA {
          states: s1,
          initial_state: i1,
          final_states: f1,
          transition: t1,
        } = r1.to_sym_fa();

        let SymFA {
          states: s2,
          initial_state: i2,
          final_states: f2,
          transition: t2,
        } = r2.to_sym_fa();

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

        SymFA {
          states,
          initial_state,
          final_states,
          transition,
        }
      }
      Regex::Not(r) => {
        let SymFA {
          states,
          initial_state,
          final_states: f,
          transition,
        } = r.to_sym_fa();

        let final_states = &states - &f;

        SymFA {
          states,
          initial_state,
          final_states,
          transition,
        }
      }
      Regex::Star(r) => {
        let SymFA {
          states,
          initial_state: i,
          final_states: f,
          transition: t,
        } = r.to_sym_fa();

        let initial_state = Rc::new(State::new());

        let final_states = f
          .iter()
          .map(|fs| Rc::clone(fs))
          .chain(vec![Rc::clone(&initial_state)])
          .collect();

        let transition = t
          .into_iter()
          .flat_map(|((state, phi), next)| {
            if state == i {
              f.iter()
                .map(|final_state| ((Rc::clone(final_state), Rc::clone(&phi)), Rc::clone(&next)))
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

        SymFA {
          states,
          initial_state,
          final_states,
          transition,
        }
      }
    }
  }
}
impl Regex<char> {
  /**
   * create new Regex from &str.\
   * possible errors: NOT_ENOUGH_ARGUMENT, NO_INPUT
   */
  pub fn new(input: &str) -> Result<Regex<char>, &'static str> {
    let fragments = split_with_bracket_and_identifier(input)?;
    let mut fragments = fragments.iter();
    let mut result = match fragments.next() {
      Some(frg) => {
        let frg = *frg;

        let head = match frg.chars().next() {
          Some(c) => c,
          None => return Err(NO_INPUT),
        };

        if frg.matches(is_identifier).next().is_some() && 1 < frg.len() {
          Regex::new(frg)?
        } else if is_binary_operator(head) || is_mono_operator(head) {
          return Err(NOT_ENOUGH_ARGUMENT);
        } else if is_constant_operator(head) {
          Regex::to_regex(head)
        } else {
          let mut chars = frg.chars();
          let last_reg = match chars.next_back() {
            Some(last) => Regex::Element(last),
            None => unreachable!(),
          };
          chars.rfold(last_reg, |acc, x| {
            Regex::Concat(Box::new(Regex::Element(x)), Box::new(acc))
          })
        }
      }
      None => return Err(NO_INPUT),
    };

    while let Some(frg) = fragments.next() {
      let frg = *frg;
      let head = match frg.chars().next() {
        Some(c) => c,
        None => return Err(NO_INPUT),
      };

      result = if frg.matches(is_identifier).next().is_some() && 1 < frg.len() {
        result.apply('#', Some(Regex::new(frg)?))?
      } else if is_binary_operator(head) {
        let next = match fragments.next() {
          Some(n) => *n,
          None => return Err(NOT_ENOUGH_ARGUMENT),
        };
        result.apply(head, Regex::new(next).ok())?
      } else if is_mono_operator(head) {
        result.apply(head, None)?
      } else if is_constant_operator(head) {
        result.apply('#', Some(Regex::to_regex(head)))?
      } else {
        let mut chars = frg.chars();
        let last_reg = match chars.next_back() {
          Some(last) => Regex::Element(last),
          None => unreachable!(),
        };
        result.apply(
          '#',
          Some(chars.rfold(last_reg, |acc, x| {
            Regex::Concat(Box::new(Regex::Element(x)), Box::new(acc))
          })),
        )?
      }
    }

    Ok(result.reduce())
  }
}
impl Recognizable<char> for Regex<char> {
  fn run(&self, _: &[char]) -> bool {
    false
  }
}

fn is_binary_operator(c: char) -> bool {
  c == '#' || c == '|'
}
fn is_mono_operator(c: char) -> bool {
  c == '*' || c == '~'
}
fn is_constant_operator(c: char) -> bool {
  c == '!' || c == '_'
}
/**
 * '#': Concat, \
 * '|': Or, \
 * '*': Star, \
 * '~': Not, \
 * '!': Empty, \
 * '_': All,
 */
fn is_identifier(c: char) -> bool {
  is_binary_operator(c) || is_mono_operator(c) || is_constant_operator(c)
}

/**
 * split string with first level '(' and ')' \
 * example: "xap(cds(cdsc)cds)cdwv(dcd)cc" to [xap, cds(cdsc)cds, cdwv, dcd, cc] \
 * possible errors: NO_MATCHING_BRA, UNNECESSARY_BRACKET, NO_MATCHING_CKET
 */
fn split_with_bracket_and_identifier<'a>(input: &'a str) -> Result<Vec<&'a str>, &'static str> {
  let chars = input.chars().enumerate();
  let mut depth = 0;
  let mut start = 0;
  let mut result = Vec::<&'a str>::new();

  for (i, c) in chars {
    if depth == 0 {
      if c == '(' {
        if start < i {
          result.push(&input[start..i]);
        }
        start = i + 1;
        depth += 1;
      } else if c == ')' {
        return Err(NO_MATCHING_BRA);
      } else if is_identifier(c) {
        if start < i {
          result.push(&input[start..i]);
        }
        result.push(&input[i..(i + 1)]);
        start = i + 1;
      }
    } else {
      if c == ')' {
        depth -= 1;
        if depth == 0 {
          if start == i {
            return Err(UNNECESSARY_BRACKET);
          }
          result.push(&input[start..i]);
          start = i + 1;
        }
      } else if c == '(' {
        depth += 1;
      }
    }
  }

  if depth != 0 {
    Err(NO_MATCHING_CKET)
  } else {
    if start < input.len() {
      result.push(&input[start..]);
    }
    Ok(result)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn is_identifier_test() {
    assert!(is_identifier('|'));
    assert!(is_identifier('*'));
    assert!(is_identifier('!'));
    assert!(!is_identifier('a'));
    assert!(!is_identifier('+'));
  }

  #[test]
  fn split_with_bracket_and_identifier_test() {
    let input = "vfdsvfdsvfsfs";
    assert_eq!(split_with_bracket_and_identifier(input), Ok(vec![input]));

    let input = "xap(cds(cdsc)cds)cdwv(dcd)cc";
    assert_eq!(
      split_with_bracket_and_identifier(input),
      Ok(vec!["xap", "cds(cdsc)cds", "cdwv", "dcd", "cc"])
    );

    let input = "()";
    assert_eq!(
      split_with_bracket_and_identifier(input),
      Err(UNNECESSARY_BRACKET)
    );

    let input = "(avcds(cdscds)cddd";
    assert_eq!(
      split_with_bracket_and_identifier(input),
      Err(NO_MATCHING_CKET)
    );

    let input = "(cdscds)dsc)cdcd(cdscds)cd";
    assert_eq!(
      split_with_bracket_and_identifier(input),
      Err(NO_MATCHING_BRA)
    );

    let input = "(aa*a|a~)*v!*c(d|b)dd!";
    assert_eq!(
      split_with_bracket_and_identifier(input),
      Ok(vec!["aa*a|a~", "*", "v", "!", "*", "c", "d|b", "dd", "!"])
    );
  }

  #[test]
  fn parse_element_test() {
    let a = Regex::Element('a');
    assert_eq!(Regex::new("a"), Ok(a));
  }

  #[test]
  fn parse_concat_test() {
    let a = Regex::Element('a');
    let a = Box::new(a);
    let b = Box::new(Regex::Element('b'));
    let c = Box::new(Regex::Element('c'));
    let bc = Box::new(Regex::Concat(b, c));
    let abc = Regex::Concat(a, bc);
    assert_eq!(Regex::new("abc"), Ok(abc));
  }

  #[test]
  fn parse_or_test() {
    let a = Box::new(Regex::Element('a'));
    let b = Box::new(Regex::Element('b'));
    let a_or_b = Regex::Or(a, b);
    assert_eq!(Regex::new("a|b"), Ok(a_or_b));
  }

  fn parse_star_test() {
    let a = Box::new(Regex::Element('a'));
    let a_star = Regex::Star(a);
    assert_eq!(Regex::new("a*"), Ok(a_star));

    let b_star_a = Regex::Concat(
      Box::new(Regex::Star(Box::new(Regex::Element('b')))),
      Box::new(Regex::Element('a')),
    );
    assert_eq!(Regex::new("b*a"), Ok(b_star_a));
  }

  #[test]
  fn parse_emp_eps_test() {
    assert_eq!(Regex::new("!"), Ok(Regex::Empty));
    assert_eq!(Regex::new("!*"), Ok(Regex::Epsilon));
  }

  #[test]
  fn parse_test() {
    assert_eq!(
      Regex::new("a((b|d)*)|!"),
      Ok(Regex::Concat(
        Box::new(Regex::Element('a')),
        Box::new(Regex::Star(Box::new(Regex::Or(
          Box::new(Regex::Element('b')),
          Box::new(Regex::Element('d'))
        ))))
      ))
    )
  }
}
