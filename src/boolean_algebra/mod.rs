use crate::transducer::term::{FunctionTerm, Lambda};
use std::{borrow::Borrow, fmt::Debug, hash::Hash, rc::Rc};

/** express effective Boolean Algebra A, tuple of (D, Phi, [], top, bot, and, or, not) \
 * D: a set of domain elements
 * Phi: a set of predicates closed under boolean connectives and checkable to its satisfiability in a polynomial time
 * []: denotational function, Phi -> 2^D (implemented as Phi -> D -> bool, need to check in class P)
 * top: [top] -> D
 * bot: [bot] -> {}
 * and: [p and q] -> [p] ++ [q]
 * or: [p or q] -> [p] || [q]
 * not: [not p] -> D \ [p]
 */
pub trait BoolAlg: Debug + PartialEq + Eq + Hash {
  type Domain: Debug + PartialEq + Eq + Hash;

  fn and(self: &Rc<Self>, other: &Rc<Self>) -> Self;
  fn or(self: &Rc<Self>, other: &Rc<Self>) -> Self;
  fn not(self: &Rc<Self>) -> Self;
  fn top() -> Self;
  fn bot() -> Self;

  /** apply argument to self and return the result */
  fn denotate(&self, arg: &Self::Domain) -> bool;
}

/**
 * for Primitive Predicate
 */
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Predicate<T>
where
  T: PartialOrd + Ord + Copy + PartialEq + Eq + Hash + Debug,
{
  Bool(bool),
  Eq(T),
  Range {
    //whether satisfying arg left <= arg && arg < right
    left: Option<T>,
    right: Option<T>,
  },
  InSet(Vec<T>),
  And(Rc<Self>, Rc<Self>),
  Or(Rc<Self>, Rc<Self>),
  Not(Rc<Self>),
  WithLambda {
    p: Rc<Predicate<T>>,
    f: Rc<Lambda<Self>>,
  },
}
impl<T> Predicate<T>
where
  T: PartialOrd + Ord + Copy + PartialEq + Eq + Hash + Debug,
{
  pub fn eq(a: T) -> Self {
    Predicate::Eq(a)
  }

  pub fn range(left: Option<T>, right: Option<T>) -> Self {
    match (&left, &right) {
      (Some(l), Some(r)) => {
        if *r < *l {
          Predicate::Bool(false)
        } else if *r == *l {
          Predicate::Eq(*l)
        } else {
          Predicate::Range { left, right }
        }
      }
      (None, None) => Predicate::Bool(true),
      _ => Predicate::Range { left, right },
    }
  }

  pub fn in_set(elements: &[T]) -> Self {
    if elements.len() == 1 {
      Predicate::eq(elements[0])
    } else {
      Predicate::InSet(Vec::from(elements))
    }
  }

  pub fn with_lambda(self: Rc<Self>, f: Rc<Lambda<Self>>) -> Self {
    Predicate::WithLambda {
      p: self.reduce(),
      f,
    }
  }

  /**
   * if any children formulas have been reduced, there is no need to reduce recursively
   */
  fn reduce(self: Rc<Self>) -> Rc<Self> {
    match self.borrow() {
      Predicate::And(p, q) => match (p.borrow(), q.borrow()) {
        (Predicate::Bool(b), _) => {
          if *b {
            Rc::clone(p)
          } else {
            Rc::clone(q)
          }
        }
        (_, Predicate::Bool(b)) => {
          if *b {
            Rc::clone(q)
          } else {
            Rc::clone(p)
          }
        }
        (Predicate::Eq(l), Predicate::Eq(r)) => {
          if l == r {
            Rc::clone(p)
          } else {
            let left = Some(std::cmp::min(*l, *r));
            let right = Some(std::cmp::max(*l, *r));
            Rc::new(Predicate::Range { left, right })
          }
        }
        (
          Predicate::Eq(e),
          Predicate::Range {
            left: Some(ref l),
            right: Some(ref r),
          },
        ) if *l <= *e && *e <= *r => Rc::clone(q),
        (
          Predicate::Range {
            left: Some(ref l),
            right: Some(ref r),
          },
          Predicate::Eq(e),
        ) if *l <= *e && *e <= *r => Rc::clone(p),
        (
          Predicate::Range {
            left: ref pl,
            right: ref pr,
          },
          Predicate::Range {
            left: ref ql,
            right: ref qr,
          },
        ) => {
          /* reduce if two range have common area. */
          match (pl, pr, ql, qr) {
            /* q -- |ql\_______/qr| */
            (Some(pl), Some(pr), Some(ql), Some(qr)) if *ql <= *pr && *pl <= *qr => {
              if *ql < *pl {
                if *qr < *pr {
                  Rc::new(Predicate::range(Some(*pl), Some(*qr)))
                } else {
                  Rc::clone(p)
                }
              } else {
                if *qr <= *pr {
                  Rc::clone(q)
                } else {
                  Rc::new(Predicate::range(Some(*ql), Some(*pr)))
                }
              }
            }
            (Some(pl), None, Some(ql), Some(qr)) if *pl <= *qr => {
              if *pl <= *ql {
                Rc::clone(q)
              } else {
                Rc::new(Predicate::range(Some(*pl), Some(*qr)))
              }
            }
            (None, Some(pr), Some(ql), Some(qr)) if *ql <= *pr => {
              if *qr <= *pr {
                Rc::clone(q)
              } else {
                Rc::new(Predicate::range(Some(*ql), Some(*pr)))
              }
            }
            /* q -- |_______/qr| */
            (Some(pl), Some(pr), None, Some(qr)) if *pl <= *qr => {
              if *pr <= *qr {
                Rc::clone(p)
              } else {
                Rc::new(Predicate::range(Some(*pl), Some(*qr)))
              }
            }
            (Some(pl), None, None, Some(qr)) => Rc::new(Predicate::range(Some(*pl), Some(*qr))),
            (None, Some(pr), None, Some(qr)) => {
              if *qr <= *pr {
                Rc::clone(q)
              } else {
                Rc::clone(p)
              }
            }
            /* q -- |ql\_______| */
            (Some(pl), Some(pr), Some(ql), None) if *ql <= *pr => {
              if *ql <= *pl {
                Rc::clone(p)
              } else {
                Rc::new(Predicate::range(Some(*ql), Some(*pr)))
              }
            }
            (Some(pl), None, Some(ql), None) => {
              if *pl <= *ql {
                Rc::clone(q)
              } else {
                Rc::clone(p)
              }
            }
            (None, Some(pr), Some(ql), None) => Rc::new(Predicate::range(Some(*ql), Some(*pr))),
            _ => Rc::new(Predicate::Bool(false)),
          }
        }
        (Predicate::Range { left: _, right: _ }, Predicate::InSet(els)) => {
          Rc::new(Predicate::in_set(
            &els
              .into_iter()
              .filter_map(|e| if p.denotate(e) { Some(e.clone()) } else { None })
              .collect::<Vec<_>>(),
          ))
        }
        _ => Rc::new(Predicate::Bool(false)),
      },
      _ => self,
    }
  }
}
impl<T> BoolAlg for Predicate<T>
where
  T: PartialOrd + Ord + Copy + PartialEq + Eq + Hash + Debug,
{
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
    Predicate::Bool(true)
  }

  fn bot() -> Self {
    Predicate::Bool(false)
  }

  fn denotate(&self, arg: &Self::Domain) -> bool {
    match self {
      Predicate::Bool(b) => *b,
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
      Predicate::Range {
        left: Some('c'),
        right: None
      },
      bigger_than_c
    );
    let bigger_than_c = bigger_than_c;
    assert!(!bigger_than_c.denotate(arg_b));
    assert!(bigger_than_c.denotate(arg_f));
    assert!(bigger_than_c.denotate(arg_z));

    let smaller_than_v = Predicate::range(None, Some('v'));
    assert_eq!(
      Predicate::Range {
        left: None,
        right: Some('v')
      },
      smaller_than_v
    );
    let smaller_than_v = smaller_than_v;
    assert!(smaller_than_v.denotate(arg_b));
    assert!(smaller_than_v.denotate(arg_f));
    assert!(!smaller_than_v.denotate(arg_z));

    let between_f_k = Predicate::range(Some('f'), Some('k'));
    assert_eq!(
      Predicate::Range {
        left: Some('f'),
        right: Some('k')
      },
      between_f_k
    );
    let between_f_k = between_f_k;
    assert!(!between_f_k.denotate(arg_b));
    assert!(between_f_k.denotate(arg_f));
    assert!(between_f_k.denotate(&'i'));
    assert!(!between_f_k.denotate(arg_z));

    let top = Predicate::range(None, None);
    assert_eq!(Predicate::Bool(true), top);
    let top = top;
    assert!(top.denotate(arg_b));
    assert!(top.denotate(arg_f));
    assert!(top.denotate(arg_z));

    let err = Predicate::range(Some('k'), Some('f'));
    assert_eq!(Predicate::Bool(false), err);
    let bot = err;
    assert!(!bot.denotate(arg_b));
    assert!(!bot.denotate(arg_f));
    assert!(!bot.denotate(arg_z));

    let eq = Predicate::range(Some('f'), Some('f'));
    assert_eq!(Predicate::Eq('f'), eq);
    let eq = eq;
    assert!(!eq.denotate(arg_b));
    assert!(eq.denotate(arg_f));
    assert!(!eq.denotate(arg_z));
  }

  #[test]
  fn in_set_test() {
    let avd = &"avd".chars().collect::<Vec<char>>()[..];
    let avd = Predicate::in_set(avd);
    assert_eq!(Predicate::InSet(vec!['a', 'v', 'd']), avd);

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
    let cond_num = Rc::new(Predicate::range(Some('0'), Some('9')));
    let cond_set_xyz = Rc::new(Predicate::in_set(&['x', 'y', 'z']));

    let cnst;
    let map;
    let fnc;
    {
      let fnc_cond1 = Rc::new(Predicate::range(Some('f'), Some('l'))); //f, g, h, i, j, k
      let fnc_cond2 = Rc::new(Predicate::in_set(&['b', 's', 'w']));

      cnst = Rc::new(Lambda::<Predicate<char>>::Constant('x'));
      map = Rc::new(Lambda::<Predicate<char>>::Mapping(vec![
        ('a', 'x'),
        ('b', 'y'),
        ('c', 'z'),
      ]));
      fnc = Rc::new(Lambda::<Predicate<char>>::Function(vec![
        (fnc_cond1.clone(), '1'),
        (fnc_cond2.clone(), '2'),
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
