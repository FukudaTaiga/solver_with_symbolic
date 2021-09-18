#![allow(dead_code)]
use std::cmp::PartialOrd;
use super::recognizable;

const NO_INPUT: &str = "Parse Error: No lefthand input found";
//const OPERATOR_EXPECTED: &str = "Parse Error: Operator Expected";
const NOT_ENOUGH_ARGUMENT: &str = "Parse Error:  Not enough argument of some operator";
const INVALID_OPERATION: &str = "Unreachable: Invalid operation";
const NO_MATCHING_BRA: &str = "Parse Error: No matching bracket '(' found";
const NO_MATCHING_CKET: &str = "Parse Error: No matching bracket ')' found";
const UNNECESSARY_BRACKET: &str = "Parse Error: Unnecessary brackets found";

#[derive(Debug, PartialEq)]
pub enum Regex<T: PartialOrd> {
  Empty,
  Epsilon,
  Element(T),
  Concat(Box<Regex<T>>, Box<Regex<T>>),
  Or(Box<Regex<T>>, Box<Regex<T>>),
  Star(Box<Regex<T>>),
  Not(Box<Regex<T>>),
  Range(T, T),
  All,
}
impl Regex<char> {
  fn new(input: String) -> Result<Regex<char>, &'static str> {
    let separated = split_with_bracket_and_identifier(input)?;
    let len = separated.len();

    if len == 0 {
      Err(NO_INPUT)
    } else if len == 1 {
      let mut chars = separated[0].chars();
      match chars.next_back() {
        Some(last) => {
          if is_identifier(last) {
            match last {
              '!' => Ok(Regex::Empty),
              '_' => Ok(Regex::All),
              _ => Err(NOT_ENOUGH_ARGUMENT),
            }
          } else {
            Ok(chars.rfold(Regex::Element(last), |acc, c| {
              let reg = Regex::Element(c);
              Regex::Concat(Box::new(reg), Box::new(acc))
            }))
          }
        }
        None => Err(NO_INPUT),
      }
    } else {
      let mut iter = separated.iter();
      let mut result: Option<Regex<char>> = None;

      while let Some(s) = iter.next() {
        let identifier = match (*s).chars().next() {
          Some(c) => c,
          None => unreachable!(),
        };

        if is_identifier(identifier) {
          match identifier {
            '|' => match (result, iter.next()) {
              (Some(r), Some(x)) => {
                result = Some(r.apply(identifier, Regex::new((*x).clone()).ok())?)
                //bad code
              }
              (_, _) => return Err(NOT_ENOUGH_ARGUMENT),
            },
            '*' | '~' => {
              result = match result {
                Some(r) => Some(r.apply(identifier, None)?),
                None => return Err(NOT_ENOUGH_ARGUMENT),
              }
            }
            '!' | '_' => {
              result = match result {
                Some(r) => Some(r.apply(identifier, None)?),
                None => Some(Regex::new((*s).clone())?), //bad code
              }
            }
            _ => unreachable!(),
          }
        } else {
          result = match result {
            Some(r) => Some(r.apply('#', Regex::new((*s).clone()).ok())?), //bad code
            None => Some(Regex::new((*s).clone())?),                       //bad code
          }
        }
      }

      match result {
        Some(r) => Ok(r),
        None => unreachable!(),
      }
    }
  }

  fn apply(self, op: char, other: Option<Regex<char>>) -> Result<Regex<char>, &'static str> {
    match (op, other) {
      ('#', Some(r)) => Ok(Regex::Concat(Box::new(self), Box::new(r))),
      ('|', Some(r)) => Ok(Regex::Or(Box::new(self), Box::new(r))),
      ('*', None) => Ok(Regex::Star(Box::new(self))),
      ('~', None) => Ok(Regex::Not(Box::new(self))),
      ('!', None) => Ok(Regex::Concat(Box::new(self), Box::new(Regex::Empty))),
      ('_', None) => Ok(Regex::Concat(Box::new(self), Box::new(Regex::All))),
      (_, _) => Err(INVALID_OPERATION),
    }
  }
}

/**
 * '#': Concat
 * '|': Or
 * '*': Star
 * '~': Not
 * '!': Empty
 * '_': All
 */
fn is_identifier(c: char) -> bool {
  match c {
    '|' | '*' | '~' | '!' | '_' | '#' => true,
    _ => false,
  }
}
/**
 * split string with first level '(' and ')'
 * example: "xap(cds(cdsc)cds)cdwv(dcd)cc" -> [xap, cds(cdsc)cds, cdwv, dcd, cc]
 */
fn split_with_bracket_and_identifier(input: String) -> Result<Vec<String>, &'static str> {
  let chars = input.chars();
  let mut depth = 0;
  let mut acc = String::new();
  let mut result = Vec::<String>::new();

  for c in chars {
    if depth == 0 {
      if c == '(' {
        if !acc.is_empty() {
          result.push(acc.clone());
          acc.clear();
        }
        depth += 1;
      } else if c == ')' {
        return Err(NO_MATCHING_BRA);
      } else if is_identifier(c) {
        if !acc.is_empty() {
          result.push(acc.clone());
          acc.clear();
        }
        result.push(c.to_string());
      } else {
        acc.push(c);
      }
    } else {
      if c == ')' {
        depth -= 1;
        if depth == 0 {
          if acc.is_empty() {
            return Err(UNNECESSARY_BRACKET);
          }
          result.push(acc.clone());
          acc.clear();
        } else {
          acc.push(c);
        }
      } else if c == '(' {
        depth += 1;
        acc.push(c);
      } else {
        acc.push(c);
      }
    }
  }

  if depth != 0 {
    Err(NO_MATCHING_CKET)
  } else {
    if !acc.is_empty() {
      result.push(acc);
    }
    Ok(result)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn vec_to_string(v: Vec<&str>) -> Vec<String> {
    v.iter().map(|s| s.to_string()).collect::<Vec<String>>()
  }

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
    let input = "vfdsvfdsvfsfs".to_string();
    let output = vec![input.clone()];
    assert_eq!(split_with_bracket_and_identifier(input), Ok(output));

    let input = "xap(cds(cdsc)cds)cdwv(dcd)cc".to_string();
    let output = vec!["xap", "cds(cdsc)cds", "cdwv", "dcd", "cc"];
    assert_eq!(
      split_with_bracket_and_identifier(input),
      Ok(vec_to_string(output))
    );

    let input = "()".to_string();
    assert_eq!(
      split_with_bracket_and_identifier(input),
      Err(UNNECESSARY_BRACKET)
    );

    let input = "(avcds(cdscds)cddd".to_string();
    assert_eq!(
      split_with_bracket_and_identifier(input),
      Err(NO_MATCHING_CKET)
    );

    let input = "(cdscds)dsc)cdcd(cdscds)cd".to_string();
    assert_eq!(
      split_with_bracket_and_identifier(input),
      Err(NO_MATCHING_BRA)
    );

    let input = "(aa*a|a~)*v!*c(d|b)dd!".to_string();
    let output = vec!["aa*a|a~", "*", "v", "!", "*", "c", "d|b", "dd", "!"];
    assert_eq!(
      split_with_bracket_and_identifier(input),
      Ok(vec_to_string(output))
    );
  }

  #[test]
  fn parse_test() {
    let a = Regex::Element('a');
    assert_eq!(Regex::new("a".to_string()), Ok(a));

    let a = Regex::Element('a');
    let a = Box::new(a);
    let b = Box::new(Regex::Element('b'));
    let c = Box::new(Regex::Element('c'));
    let bc = Box::new(Regex::Concat(b, c));
    let abc = Regex::Concat(a, bc);
    assert_eq!(Regex::new("abc".to_string()), Ok(abc));

    let a = Box::new(Regex::Element('a'));
    let b = Box::new(Regex::Element('b'));
    let a_or_b = Regex::Or(a, b);
    assert_eq!(Regex::new("a|b".to_string()), Ok(a_or_b));

    let a = Box::new(Regex::Element('a'));
    let a_star = Regex::Star(a);
    assert_eq!(Regex::new("a*".to_string()), Ok(a_star));

    assert_eq!(Regex::new("!".to_string()), Ok(Regex::Empty));

    assert_eq!(
      Regex::new("!*".to_string()),
      Ok(Regex::Star(Box::new(Regex::Empty)))
    );

    assert_eq!(
      Regex::new("a((b|d)*)|!".to_string()),
      Ok(Regex::Or(
        Box::new(Regex::Concat(
          Box::new(Regex::Element('a')),
          Box::new(Regex::Star(Box::new(Regex::Or(
            Box::new(Regex::Element('b')),
            Box::new(Regex::Element('d'))
          ))))
        )),
        Box::new(Regex::Empty)
      ))
    )
  }
}
