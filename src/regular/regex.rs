use super::{recognizable::Recognizable, symbolic_automata::Sfa};
use crate::{
  boolean_algebra::{BoolAlg, Predicate},
  char_util::FromChar,
  smt2,
  state::StateImpl,
};
use smt2parser::concrete::{Constant, Term};
use std::{
  collections::{HashMap, HashSet},
  fmt::Debug,
  hash::Hash,
};

//Errors
const NO_INPUT: &str = "Parse Error: No lefthand input found";
//const OPERATOR_EXPECTED: &str = "Parse Error: Operator Expected";
const NOT_ENOUGH_ARGUMENT: &str = "Parse Error:  Not enough argument of some operator";
const INVALID_OPERATION: &str = "Unreachable: Invalid operation";
const NO_MATCHING_BRA: &str = "Parse Error: No matching bracket '(' found";
const NO_MATCHING_CKET: &str = "Parse Error: No matching bracket ')' found";
const UNNECESSARY_BRACKET: &str = "Parse Error: Unnecessary brackets found";

/**
 * may prefer Rc to Box.
 * but Regex size won't go so large, Box will be enough.
 */
#[derive(Debug, PartialEq, Clone)]
pub enum Regex<T: PartialOrd> {
  Empty,
  Epsilon,
  All,
  Element(T),
  Range(Option<T>, Option<T>),
  Concat(Box<Regex<T>>, Box<Regex<T>>),
  Or(Box<Regex<T>>, Box<Regex<T>>),
  Inter(Box<Regex<T>>, Box<Regex<T>>),
  Star(Box<Regex<T>>),
  Not(Box<Regex<T>>),
}
impl<T> Regex<T>
where
  T: PartialOrd + Ord + Copy + PartialEq + Eq + Hash + Debug,
{
  pub fn concat(self, other: Regex<T>) -> Self {
    Regex::Concat(Box::new(self), Box::new(other))
  }

  pub fn or(self, other: Regex<T>) -> Self {
    Regex::Or(Box::new(self), Box::new(other))
  }

  pub fn inter(self, other: Regex<T>) -> Self {
    Regex::Inter(Box::new(self), Box::new(other))
  }

  pub fn star(self) -> Self {
    Regex::Star(Box::new(self))
  }

  pub fn not(self) -> Self {
    Regex::Not(Box::new(self))
  }

  pub fn range(start: Option<T>, end: Option<T>) -> Self {
    Regex::Range(start, end)
  }

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
      Regex::Concat(r1, r2) => match (r1.reduce(), r2.reduce()) {
        (Regex::Empty, _) | (_, Regex::Empty) => Regex::Empty,
        (Regex::Epsilon, r) | (r, Regex::Epsilon) => r,
        (left, right) => Regex::Concat(Box::new(left), Box::new(right)),
      },
      Regex::Or(r1, r2) => match (r1.reduce(), r2.reduce()) {
        (Regex::Empty, r) | (r, Regex::Empty) => r,
        (left, right) => Regex::Or(Box::new(left), Box::new(right)),
      },
      Regex::Star(r) => {
        let reg = r.reduce();
        if let Regex::Empty = reg {
          Regex::Epsilon
        } else {
          Regex::Star(Box::new(reg))
        }
      }
      _ => self,
    }
  }

  //with, thompson  --- clushkul, partial derivative
  pub fn to_sym_fa<S: StateImpl>(self) -> Sfa<Predicate<T>, S> {
    match self {
      Regex::Empty => {
        let initial_state = S::new();
        let mut states = HashSet::new();
        let final_states = HashSet::new();
        let transition = HashMap::new();
        states.insert(initial_state.clone());

        Sfa::new(states, initial_state, final_states, transition)
      }
      Regex::Epsilon => {
        let initial_state = S::new();
        let mut states = HashSet::new();
        let mut final_states = HashSet::new();
        let mut transition = HashMap::new();
        let refusal_state = S::new();

        states.insert(initial_state.clone());
        states.insert(refusal_state.clone());

        final_states.insert(initial_state.clone());

        transition.insert(
          (initial_state.clone(), Predicate::top()),
          refusal_state.clone(),
        );

        Sfa::new(states, initial_state, final_states, transition)
      }
      Regex::Element(a) => {
        let initial_state = S::new();
        let mut states = HashSet::new();
        let mut final_states = HashSet::new();
        let mut transition = HashMap::new();
        let final_state = S::new();

        states.insert(initial_state.clone());
        states.insert(final_state.clone());
        final_states.insert(final_state.clone());

        transition.insert((initial_state.clone(), Predicate::eq(a)), final_state);

        Sfa::new(states, initial_state, final_states, transition)
      }
      Regex::All => {
        let initial_state = S::new();
        let mut states = HashSet::new();
        let mut final_states = HashSet::new();
        let mut transition = HashMap::new();
        let final_state = S::new();

        states.insert(initial_state.clone());
        states.insert(final_state.clone());

        final_states.insert(final_state.clone());

        transition.insert((initial_state.clone(), Predicate::top()), final_state);

        Sfa::new(states, initial_state, final_states, transition)
      }
      Regex::Range(left, right) => {
        let initial_state = S::new();
        let mut states = HashSet::new();
        let mut final_states = HashSet::new();
        let mut transition = HashMap::new();
        let final_state = S::new();

        states.insert(initial_state.clone());
        states.insert(final_state.clone());

        final_states.insert(final_state.clone());

        transition.insert(
          (initial_state.clone(), Predicate::range(left, right)),
          final_state,
        );

        Sfa::new(states, initial_state, final_states, transition)
      }
      Regex::Concat(r1, r2) => r1.to_sym_fa().concat(r2.to_sym_fa()),
      Regex::Or(r1, r2) => r1.to_sym_fa().or(r2.to_sym_fa()),
      Regex::Inter(r1, r2) => r1.to_sym_fa().inter(r2.to_sym_fa()),
      Regex::Not(r) => r.to_sym_fa().not(),
      Regex::Star(r) => r.to_sym_fa().star(),
    }
  }
}
impl<T: FromChar> Regex<T> {
  pub fn new(term: &Term) -> Self {
    match term {
      Term::Application {
        qual_identifier,
        arguments,
      } => match &smt2::get_symbol(qual_identifier)[..] {
        "str.to.re" => {
          if let [term] = &arguments[..] {
            if let Term::Constant(Constant::String(s)) = term {
              s.chars()
                .fold(Regex::Epsilon, |reg, c| {
                  reg.concat(Regex::Element(T::from_char(c)))
                })
                .reduce()
            } else {
              panic!("Syntax Error")
            }
          } else {
            panic!("Syntax Error")
          }
        }
        "re.++" => arguments
          .into_iter()
          .fold(Regex::Epsilon, |reg, term| reg.concat(Regex::new(term)))
          .reduce(),
        "re.union" => arguments
          .into_iter()
          .fold(Regex::Epsilon, |reg, term| reg.or(Regex::new(term)))
          .reduce(),
        "re.inter" => unimplemented!(),
        "re.*" => {
          if let [term] = &arguments[..] {
            Regex::new(term).reduce().star()
          } else {
            panic!("Syntax Error")
          }
        }
        "re.+" => {
          if let [term] = &arguments[..] {
            let regex = Regex::new(term).reduce();
            regex.clone().concat(regex.star())
          } else {
            panic!("Syntax Error")
          }
        }
        "re.range" => {
          if let [start, end] = &arguments[..] {
            if let Term::Constant(Constant::String(start)) = start {
              if let Term::Constant(Constant::String(end)) = end {
                let start = start.chars().next().map(|c| T::from_char(c));
                let end = end.chars().next().map(|c| T::from_char(c));
                Regex::range(start, end)
              } else {
                panic!("Syntax Error")
              }
            } else {
              panic!("Syntax Error")
            }
          } else {
            panic!("Syntax Error")
          }
        }
        _ => panic!("Syntax Error"),
      },
      Term::QualIdentifier(qi) => match &smt2::get_symbol(qi)[..] {
        "re.nostr" => Regex::Epsilon,
        "re.allchar" => Regex::All,
        _ => panic!("Syntax Error"),
      },
      _ => panic!("Syntax Error"),
    }
  }
}
impl Regex<char> {
  /**
   * create new Regex from &str.
   * possible errors: NOT_ENOUGH_ARGUMENT, NO_INPUT.
   * mainly aime to use with test.
   */
  pub fn parse(input: &str) -> Result<Self, &'static str> {
    let fragments = lexer(input)?;
    let mut fragments = fragments.iter();
    let mut result = match fragments.next() {
      Some(frg) => {
        let frg = *frg;

        let head = match frg.chars().next() {
          Some(c) => c,
          None => return Err(NO_INPUT),
        };

        if frg.matches(is_identifier).next().is_some() && 1 < frg.len() {
          Regex::parse(frg)?
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
        result.apply('#', Some(Regex::parse(frg)?))?
      } else if is_binary_operator(head) {
        let next = match fragments.next() {
          Some(n) => *n,
          None => return Err(NOT_ENOUGH_ARGUMENT),
        };
        result.apply(head, Regex::parse(next).ok())?
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

  pub fn convert<U: FromChar>(self) -> Regex<U> {
    match self {
      Regex::Empty => Regex::Empty,
      Regex::Epsilon => Regex::Epsilon,
      Regex::All => Regex::All,
      Regex::Element(c) => Regex::Element(U::from_char(c)),
      Regex::Range(l, r) => Regex::range(l.map(|c| U::from_char(c)), r.map(|c| U::from_char(c))),
      Regex::Or(r1, r2) => Regex::Or(Box::new(r1.convert()), Box::new(r2.convert())),
      Regex::Inter(r1, r2) => Regex::Inter(Box::new(r1.convert()), Box::new(r2.convert())),
      Regex::Concat(r1, r2) => Regex::Concat(Box::new(r1.convert()), Box::new(r2.convert())),
      Regex::Not(r) => Regex::Not(Box::new(r.convert())),
      Regex::Star(r) => Regex::Star(Box::new(r.convert())),
    }
  }
}
impl Recognizable<char> for Regex<char> {
  fn member(&self, _: &[char]) -> bool {
    unimplemented!()
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
fn lexer<'a>(input: &'a str) -> Result<Vec<&'a str>, &'static str> {
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
  fn lexer_test() {
    let input = "vfdsvfdsvfsfs";
    assert_eq!(lexer(input), Ok(vec![input]));

    let input = "xap(cds(cdsc)cds)cdwv(dcd)cc";
    assert_eq!(
      lexer(input),
      Ok(vec!["xap", "cds(cdsc)cds", "cdwv", "dcd", "cc"])
    );

    let input = "()";
    assert_eq!(lexer(input), Err(UNNECESSARY_BRACKET));

    let input = "(avcds(cdscds)cddd";
    assert_eq!(lexer(input), Err(NO_MATCHING_CKET));

    let input = "(cdscds)dsc)cdcd(cdscds)cd";
    assert_eq!(lexer(input), Err(NO_MATCHING_BRA));

    let input = "(aa*a|a~)*v!*c(d|b)dd!";
    assert_eq!(
      lexer(input),
      Ok(vec!["aa*a|a~", "*", "v", "!", "*", "c", "d|b", "dd", "!"])
    );
  }

  #[test]
  fn parse_element() {
    let a = Regex::Element('a');
    assert_eq!(Regex::parse("a"), Ok(a));
  }

  #[test]
  fn parse_concat() {
    let a = Regex::Element('a');
    let a = Box::new(a);
    let b = Box::new(Regex::Element('b'));
    let c = Box::new(Regex::Element('c'));
    let bc = Box::new(Regex::Concat(b, c));
    let abc = Regex::Concat(a, bc);
    assert_eq!(Regex::parse("abc"), Ok(abc));
  }

  #[test]
  fn parse_or() {
    let a = Box::new(Regex::Element('a'));
    let b = Box::new(Regex::Element('b'));
    let a_or_b = Regex::Or(a, b);
    assert_eq!(Regex::parse("a|b"), Ok(a_or_b));
  }

  #[test]
  fn parse_star() {
    let a = Box::new(Regex::Element('a'));
    let a_star = Regex::Star(a);
    assert_eq!(Regex::parse("a*"), Ok(a_star));

    let b_star_a = Regex::Concat(
      Box::new(Regex::Star(Box::new(Regex::Element('b')))),
      Box::new(Regex::Element('a')),
    );
    assert_eq!(Regex::parse("b*a"), Ok(b_star_a));
  }

  #[test]
  fn parse_empty_and_epsilon() {
    assert_eq!(Regex::parse("!"), Ok(Regex::Empty));
    assert_eq!(Regex::parse("!*"), Ok(Regex::Epsilon));
  }

  #[test]
  fn parse() {
    assert_eq!(
      Regex::parse("a((b|d)*)|!"),
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
