#![allow(dead_code)]
use crate::transducer::term::{FunctionTerm, Lambda};
use std::rc::Rc;

/**
 * express effective Boolean Algebra A, tuple of (D, Phi, [], top, bot, and, or, not) \
 * D: a set of domain elements \
 * Phi: a set of predicates closed under boolean connectives and checkable to its satisfiability in a polynomial time \
 * []: denotational function, Phi -> 2^D (implemented as Phi -> D -> bool, need to check in class P) \
 * top: [top] -> D \
 * bot: [bot] -> {} \
 * and: [p and q] -> [p] ++ [q] \
 * or: [p or q] -> [p] || [q] \
 * not: [not p] -> D \ [p] \
 *
 * WIP
 */
pub trait BoolAlg {
  type Domain;

  fn and(self: &Rc<Self>, other: &Rc<Self>) -> Self;
  fn or(self: &Rc<Self>, other: &Rc<Self>) -> Self;
  fn not(self: &Rc<Self>) -> Self;
  fn top() -> Self;
  fn bot() -> Self;

  fn denotate(&self, arg: &Self::Domain) -> bool;
}

const INVALID_RANGE: &str = "Invalid range Error: left argument should be smaller than right";

/**
 * for Primitive Predicate
 */
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Predicate<'a, T: PartialOrd + Copy + Eq> {
  Top,
  Bot,
  Eq(T),
  Range {
    //whether satisfying arg left <= arg && arg < right
    left: Option<T>,
    right: Option<T>,
  },
  InSet(&'a [T]),
  And(Rc<Self>, Rc<Self>),
  Or(Rc<Self>, Rc<Self>),
  Not(Rc<Self>),
  WithLambda {
    p: Rc<Predicate<'a, T>>,
    f: Rc<Lambda<Self>>,
  },
}
impl<'a, T: PartialOrd + Copy + Eq> Predicate<'a, T> {
  pub fn eq(a: T) -> Self {
    Predicate::Eq(a)
  }

  pub fn range(left: Option<T>, right: Option<T>) -> Result<Self, &'static str> {
    match (&left, &right) {
      (Some(l), Some(r)) => {
        if *r < *l {
          Err(INVALID_RANGE)
        } else if *r == *l {
          Ok(Predicate::Eq(*l))
        } else {
          Ok(Predicate::Range { left, right })
        }
      }
      (None, None) => Ok(Predicate::Top),
      _ => Ok(Predicate::Range { left, right }),
    }
  }

  pub fn in_set(elements: &[T]) -> Predicate<'_, T> {
    if elements.len() == 1 {
      Predicate::eq(elements[0])
    } else {
      Predicate::InSet(elements)
    }
  }

  pub fn with_lambda(self: &Rc<Self>, f: Rc<Lambda<Self>>) -> Predicate<'a, T> {
    Predicate::WithLambda {
      p: Rc::clone(&self),
      f: Rc::clone(&f),
    }
  }
}
impl<T: PartialOrd + Copy + Eq> BoolAlg for Predicate<'_, T> {
  type Domain = T;

  fn and(self: &Rc<Self>, other: &Rc<Self>) -> Self {
    Predicate::And(Rc::clone(self), Rc::clone(other))
  }

  fn or(self: &Rc<Self>, other: &Rc<Self>) -> Self {
    Predicate::Or(Rc::clone(self), Rc::clone(other))
  }

  fn not(self: &Rc<Self>) -> Self {
    Predicate::Not(Rc::clone(self))
  }

  fn top() -> Self {
    Predicate::Top
  }

  fn bot() -> Self {
    Predicate::Bot
  }

  fn denotate(&self, arg: &Self::Domain) -> bool {
    match self {
      Predicate::Top => true,
      Predicate::Bot => false,
      Predicate::Eq(a) => *a == *arg,
      Predicate::Range {
        ref left,
        ref right,
      } => {
        return match left {
          Some(l) => *l <= *arg,
          None => true,
        } && match right {
          Some(r) => *arg < *r,
          None => true,
        }
      }
      Predicate::InSet(elements) => elements.contains(arg),
      Predicate::And(ref p, ref q) => p.denotate(arg) && q.denotate(arg),
      Predicate::Or(ref p, ref q) => p.denotate(arg) || q.denotate(arg),
      Predicate::Not(ref p) => !p.denotate(arg),
      Predicate::WithLambda { ref p, ref f } => p.denotate(f.apply(arg)),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn eq_test() {
    let eq_a = Predicate::eq('a');
    assert_eq!(Predicate::Eq('a'), eq_a);

    assert!(eq_a.denotate(&'a'));
    assert!(!eq_a.denotate(&'b'));
  }

  #[test]
  fn range_test() {
    let arg_b = &'b';
    let arg_f = &'f';
    let arg_z = &'z';

    let bigger_than_c = Predicate::range(Some('c'), None);
    assert_eq!(
      Ok(Predicate::Range {
        left: Some('c'),
        right: None
      }),
      bigger_than_c
    );
    let bigger_than_c = bigger_than_c.unwrap_or(Predicate::Bot);
    assert!(!bigger_than_c.denotate(arg_b));
    assert!(bigger_than_c.denotate(arg_f));
    assert!(bigger_than_c.denotate(arg_z));

    let smaller_than_v = Predicate::range(None, Some('v'));
    assert_eq!(
      Ok(Predicate::Range {
        left: None,
        right: Some('v')
      }),
      smaller_than_v
    );
    let smaller_than_v = smaller_than_v.unwrap_or(Predicate::Bot);
    assert!(smaller_than_v.denotate(arg_b));
    assert!(smaller_than_v.denotate(arg_f));
    assert!(!smaller_than_v.denotate(arg_z));

    let between_f_k = Predicate::range(Some('f'), Some('k'));
    assert_eq!(
      Ok(Predicate::Range {
        left: Some('f'),
        right: Some('k')
      }),
      between_f_k
    );
    let between_f_k = between_f_k.unwrap_or(Predicate::Bot);
    assert!(!between_f_k.denotate(arg_b));
    assert!(between_f_k.denotate(arg_f));
    assert!(between_f_k.denotate(&'i'));
    assert!(!between_f_k.denotate(arg_z));

    let top = Predicate::range(None, None);
    assert_eq!(Ok(Predicate::Top), top);
    let top = top.unwrap_or(Predicate::Bot);
    assert!(top.denotate(arg_b));
    assert!(top.denotate(arg_f));
    assert!(top.denotate(arg_z));

    let err = Predicate::range(Some('k'), Some('f'));
    assert_eq!(Err(INVALID_RANGE), err);
    let bot = err.unwrap_or(Predicate::Bot);
    assert!(!bot.denotate(arg_b));
    assert!(!bot.denotate(arg_f));
    assert!(!bot.denotate(arg_z));

    let eq = Predicate::range(Some('f'), Some('f'));
    assert_eq!(Ok(Predicate::Eq('f')), eq);
    let eq = eq.unwrap_or(Predicate::Bot);
    assert!(!eq.denotate(arg_b));
    assert!(eq.denotate(arg_f));
    assert!(!eq.denotate(arg_z));
  }

  #[test]
  fn in_set_test() {
    let avd = &"avd".chars().collect::<Vec<char>>()[..];
    let avd = Predicate::in_set(avd);
    assert_eq!(Predicate::InSet(&['a', 'v', 'd']), avd);

    assert!(avd.denotate(&'a'));
    assert!(avd.denotate(&'v'));
    assert!(avd.denotate(&'d'));
    assert!(!avd.denotate(&'c'));
    assert!(!avd.denotate(&'h'));
    assert!(!avd.denotate(&'i'));
  }
  #[test]
  fn with_lambda_test() {
    let cond_x = Rc::new(Predicate::eq('x'));
    let cond_num = Rc::new(Predicate::range(Some('0'), Some('9')).unwrap());
    let cond_set_xyz = Rc::new(Predicate::in_set(&['x', 'y', 'z']));

    let cnst;
    let map;
    let fnc;
    {
      let fnc_cond1 = Rc::new(Predicate::range(Some('f'), Some('l')).unwrap()); //f, g, h, i, j, k
      let fnc_cond2 = Rc::new(Predicate::in_set(&['b', 's', 'w']));

      cnst = Rc::new(Lambda::<Predicate<'_, char>>::Constant('x'));
      map = Rc::new(Lambda::<Predicate<'_, char>>::Mapping(vec![
        ('a', 'x'),
        ('b', 'y'),
        ('c', 'z'),
      ]));
      fnc = Rc::new(Lambda::<Predicate<'_, char>>::Function(vec![
        (Rc::clone(&fnc_cond1), '1'),
        (Rc::clone(&fnc_cond2), '2'),
      ]));
    }

    let cond_x = cond_x.with_lambda(cnst);
    assert!(cond_x.denotate(&'a'));
    assert!(cond_x.denotate(&'x'));
    assert!(cond_x.denotate(&'z'));
    assert!(cond_x.denotate(&'9'));

    let cond_set_xyz = cond_set_xyz.with_lambda(map);
    assert!(cond_set_xyz.denotate(&'a'));
    assert!(cond_set_xyz.denotate(&'b'));
    assert!(cond_set_xyz.denotate(&'c'));
    assert!(!cond_set_xyz.denotate(&'0'));
    assert!(!cond_set_xyz.denotate(&'s'));

    let cond_num = cond_num.with_lambda(fnc);
    assert!(cond_num.denotate(&'f'));
    assert!(cond_num.denotate(&'g'));
    assert!(cond_num.denotate(&'h'));
    assert!(cond_num.denotate(&'i'));
    assert!(cond_num.denotate(&'k'));
    assert!(!cond_num.denotate(&'l'));

    assert!(cond_num.denotate(&'b'));
    assert!(cond_num.denotate(&'s'));
    assert!(cond_num.denotate(&'w'));
    assert!(!cond_num.denotate(&'p'));
    assert!(!cond_num.denotate(&'a'));
  }
}
