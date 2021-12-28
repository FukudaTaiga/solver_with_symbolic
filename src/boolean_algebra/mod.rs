use crate::char_util::FromChar;
use crate::transducer::term::{FunctionTerm, Lambda};
use std::{fmt::Debug, hash::Hash};

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
pub trait BoolAlg: Debug + PartialEq + Eq + Hash + Clone {
  type Domain: FromChar;
  type Term: FunctionTerm<Underlying = Self>;

  fn char(a: Self::Domain) -> Self;
  fn and(self: &Self, other: &Self) -> Self;
  fn or(self: &Self, other: &Self) -> Self;
  fn not(self: &Self) -> Self;
  fn top() -> Self;
  fn bot() -> Self;
  fn with_lambda(&self, f: Self::Term) -> Self;

  fn all_char() -> Self {
    //Self::char(Self::Domain::separator()).not()
    Self::top()
  }

  /** apply argument to self and return the result */
  fn denote(&self, arg: &Self::Domain) -> bool;

  fn satisfiable(&self) -> bool;
}

/**
 * for Primitive Predicate
 */
#[derive(Debug, Eq, Hash, Clone)]
pub enum Predicate<T: FromChar> {
  Bool(bool),
  Eq(T),
  /** whether satisfying arg left <= arg && arg < right */
  Range {
    left: Option<T>,
    right: Option<T>,
  },
  InSet(Vec<T>),
  And(Box<Self>, Box<Self>),
  Or(Box<Self>, Box<Self>),
  Not(Box<Self>),
  WithLambda {
    p: Box<Self>,
    f: Lambda<Self>,
  },
}
impl<T: FromChar> PartialEq for Predicate<T> {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Predicate::Bool(b1), Predicate::Bool(b2)) => !(b1 ^ b2),
      (Predicate::Eq(e1), Predicate::Eq(e2)) => e1 == e2,
      (
        Predicate::Range {
          left: l1,
          right: r1,
        },
        Predicate::Range {
          left: l2,
          right: r2,
        },
      ) => l1 == l2 && r1 == r2,
      (Predicate::InSet(els1), Predicate::InSet(els2)) => els1 == els2,
      (Predicate::And(p1, p2), Predicate::And(q1, q2)) => {
        (p1 == q1 && p2 == q2) || (p1 == q2 && p2 == q1)
      }
      (Predicate::Or(p1, p2), Predicate::Or(q1, q2)) => {
        (p1 == q1 && p2 == q2) || (p1 == q2 && p2 == q1)
      }
      (Predicate::Not(p1), Predicate::Not(p2)) => p1 == p2,
      (Predicate::WithLambda { p: p1, f: f1 }, Predicate::WithLambda { p: p2, f: f2 }) => {
        p1 == p2 && f1 == f2
      }
      _ => false,
    }
  }
}
impl<T: FromChar> Predicate<T> {
  pub fn range(left: Option<T>, right: Option<T>) -> Self {
    match (&left, &right) {
      (Some(l), Some(r)) => {
        if r < l {
          Predicate::bot()
        } else if r == l {
          Predicate::char(l.clone())
        } else {
          Predicate::Range { left, right }
        }
      }
      (None, None) => Predicate::top(),
      _ => Predicate::Range { left, right },
    }
  }

  pub fn in_set(elements: &[T]) -> Self {
    if elements.len() == 0 {
      Predicate::bot()
    } else if elements.len() == 1 {
      Predicate::char(elements[0].clone())
    } else {
      Predicate::InSet(Vec::from(elements))
    }
  }
}
impl<T: FromChar> BoolAlg for Predicate<T> {
  type Domain = T;
  type Term = Lambda<Self>;

  fn char(a: Self::Domain) -> Self {
    Predicate::Eq(a)
  }

  fn and<'a>(&'a self, other: &'a Self) -> Self {
    match (self, other) {
      (Predicate::Bool(b), p) | (p, Predicate::Bool(b)) => {
        if *b {
          p.clone()
        } else {
          Predicate::bot()
        }
      }
      (Predicate::Eq(c), p) | (p, Predicate::Eq(c)) => {
        if p.denote(c) {
          Predicate::Eq(c.clone())
        } else {
          Predicate::bot()
        }
      }
      (
        Predicate::Range {
          left: pl,
          right: pr,
        },
        Predicate::Range {
          left: ql,
          right: qr,
        },
      ) => {
        /* reduce if two range have common area. */
        match (pl, pr, ql, qr) {
          /* q is of the form |ql\_______/qr| */
          (Some(pl), Some(pr), Some(ql), Some(qr)) if *ql <= *pr && *pl <= *qr => {
            if *ql < *pl {
              if *qr < *pr {
                /* ql\__pl\_result_/qr__/pr */
                Predicate::range(Some(pl.clone()), Some(qr.clone()))
              } else {
                /* ql\__pl\_result_/pr__qr */
                self.clone()
              }
            } else {
              if *qr <= *pr {
                /* pl\__ql\_result_/qr__/pr */
                other.clone()
              } else {
                /* pl\__ql\_result_/pr__/qr */
                Predicate::range(Some(ql.clone()), Some(pr.clone()))
              }
            }
          }
          (Some(pl), None, Some(ql), Some(qr)) if *pl <= *qr => {
            if *pl <= *ql {
              other.clone()
            } else {
              Predicate::range(Some(pl.clone()), Some(qr.clone()))
            }
          }
          (None, Some(pr), Some(ql), Some(qr)) if *ql <= *pr => {
            if *qr <= *pr {
              other.clone()
            } else {
              Predicate::range(Some(ql.clone()), Some(pr.clone()))
            }
          }
          /* q is of the form |_______/qr| */
          (Some(pl), Some(pr), None, Some(qr)) if *pl <= *qr => {
            if *pr <= *qr {
              self.clone()
            } else {
              Predicate::range(Some(pl.clone()), Some(qr.clone()))
            }
          }
          (Some(pl), None, None, Some(qr)) => Predicate::range(Some(pl.clone()), Some(qr.clone())),
          (None, Some(pr), None, Some(qr)) => {
            if *qr <= *pr {
              other.clone()
            } else {
              self.clone()
            }
          }
          /* q is of the form |ql\_______| */
          (Some(pl), Some(pr), Some(ql), None) if *ql <= *pr => {
            if *ql <= *pl {
              self.clone()
            } else {
              Predicate::range(Some(ql.clone()), Some(pr.clone()))
            }
          }
          (Some(pl), None, Some(ql), None) => {
            if *pl <= *ql {
              other.clone()
            } else {
              self.clone()
            }
          }
          (None, Some(pr), Some(ql), None) => Predicate::range(Some(ql.clone()), Some(pr.clone())),
          _ => Predicate::bot(),
        }
      }
      (Predicate::InSet(els), p) | (p, Predicate::InSet(els)) => {
        let els_ = els
          .into_iter()
          .filter(|e| p.denote(e))
          .cloned()
          .collect::<Vec<_>>();
        if els_.len() == 0 {
          Predicate::bot()
        } else {
          Predicate::in_set(&els_)
        }
      }
      (Predicate::Not(p), q) | (q, Predicate::Not(p)) if *q == **p => Predicate::bot(),
      (Predicate::Not(p1), Predicate::Not(p2)) => Predicate::Not(Box::new(p1.or(p2))),
      (p, q) => {
        if *p == *q {
          p.clone()
        } else {
          Predicate::And(Box::new(p.clone()), Box::new(q.clone()))
        }
      }
    }
  }

  fn or<'a>(&'a self, other: &'a Self) -> Self {
    match (self, other) {
      (Predicate::Bool(b), p) | (p, Predicate::Bool(b)) => {
        if *b {
          Predicate::top()
        } else {
          p.clone()
        }
      }
      (Predicate::Eq(c), p) | (p, Predicate::Eq(c)) if p.denote(c) => p.clone(),
      (Predicate::Eq(c1), Predicate::Eq(c2)) => Predicate::in_set(&[c1.clone(), c2.clone()]),
      (Predicate::Eq(c), Predicate::InSet(els)) | (Predicate::InSet(els), Predicate::Eq(c)) => {
        let mut els_ = els.clone();
        els_.push(c.clone());
        Predicate::in_set(&els_)
      }
      (
        Predicate::Range {
          left: pl,
          right: pr,
        },
        Predicate::Range {
          left: ql,
          right: qr,
        },
      ) => {
        /* reduce if one range surrounds other. */
        match (pl, pr, ql, qr) {
          /* q is of the form |ql\_______/qr| */
          (Some(pl), Some(pr), Some(ql), Some(qr)) if *ql <= *pr && *pl <= *qr => {
            if *ql <= *pl {
              if *pr <= *qr {
                /* ql\__pl\______/pr__/qr */
                other.clone()
              } else {
                /* ql\__pl\_______/qr__/pr */
                Predicate::range(Some(ql.clone()), Some(pr.clone()))
              }
            } else {
              if *qr <= *pr {
                /* pl\__ql\_______/qr__/pr */
                self.clone()
              } else {
                /* pl\__ql\______/pr__/qr */
                Predicate::range(Some(pl.clone()), Some(qr.clone()))
              }
            }
          }
          (Some(pl), None, Some(ql), Some(qr)) if *pl <= *qr => {
            if *pl <= *ql {
              self.clone()
            } else {
              Predicate::range(Some(ql.clone()), None)
            }
          }
          (None, Some(pr), Some(ql), Some(qr)) if *ql <= *pr => {
            if *qr <= *pr {
              self.clone()
            } else {
              Predicate::range(None, Some(qr.clone()))
            }
          }
          /* q is of the form |_______/qr| */
          (Some(pl), Some(pr), None, Some(qr)) if *pl <= *qr => {
            if *pr <= *qr {
              other.clone()
            } else {
              Predicate::range(None, Some(pr.clone()))
            }
          }
          (Some(pl), None, None, Some(qr)) if *pl <= *qr => Predicate::top(),
          (None, Some(pr), None, Some(qr)) => {
            if *qr <= *pr {
              self.clone()
            } else {
              other.clone()
            }
          }
          /* q is of the form |ql\_______| */
          (Some(pl), Some(pr), Some(ql), None) if *ql <= *pr => {
            if *ql <= *pl {
              other.clone()
            } else {
              Predicate::range(Some(pl.clone()), None)
            }
          }
          (Some(pl), None, Some(ql), None) => {
            if *pl <= *ql {
              self.clone()
            } else {
              other.clone()
            }
          }
          (None, Some(pr), Some(ql), None) if *ql <= *pr => Predicate::top(),
          _ => Predicate::Or(Box::new(self.clone()), Box::new(other.clone())),
        }
      }
      (Predicate::InSet(els1), Predicate::InSet(els2)) => {
        let els: std::collections::HashSet<_> = els1.into_iter().chain(els2.into_iter()).collect();
        Predicate::in_set(&els.into_iter().cloned().collect::<Vec<_>>())
      }
      (Predicate::InSet(els), p) | (p, Predicate::InSet(els)) => {
        let els_ = els
          .into_iter()
          .filter(|e| !p.denote(*e))
          .cloned()
          .collect::<Vec<_>>();
        if els_.len() == 0 {
          p.clone()
        } else {
          Predicate::Or(Box::new(Predicate::in_set(&els_)), Box::new(p.clone()))
        }
      }
      (Predicate::Not(p), q) | (q, Predicate::Not(p)) if **p == *q => Predicate::top(),
      (Predicate::Not(p1), Predicate::Not(p2)) => Predicate::Not(Box::new(p1.and(p2))),
      (p, q) => {
        if *p == *q {
          p.clone()
        } else {
          Predicate::Or(Box::new(p.clone()), Box::new(q.clone()))
        }
      }
    }
  }

  fn not(&self) -> Self {
    match self {
      Predicate::Not(p) => (**p).clone(),
      Predicate::Bool(b) => Predicate::Bool(!b),
      p => Predicate::Not(Box::new(p.clone())),
    }
  }

  fn top() -> Self {
    Predicate::Bool(true)
  }

  fn bot() -> Self {
    Predicate::Bool(false)
  }

  fn with_lambda(&self, f: Self::Term) -> Self {
    match f {
      Lambda::Id => self.clone(),
      Lambda::Constant(c) => {
        if self.denote(&c) {
          Predicate::top()
        } else {
          Predicate::bot()
        }
      }
      f => match self {
        Predicate::Bool(b) => {
          if *b {
            Predicate::top()
          } else {
            Predicate::bot()
          }
        }
        Predicate::WithLambda { p, f: f2 } => Predicate::WithLambda {
          p: p.clone(),
          f: f.compose(f2.clone()),
        },
        _ => Predicate::WithLambda {
          p: Box::new(self.clone()),
          f,
        },
      },
    }
  }

  fn denote(&self, arg: &Self::Domain) -> bool {
    match self {
      Predicate::Bool(b) => *b,
      Predicate::Eq(a) => *a == *arg,
      Predicate::Range {
        left,
        right,
      } => {
        left.as_ref().map(|l| *l <= *arg).unwrap_or(true)
          && right.as_ref().map(|r| *arg < *r).unwrap_or(true)
      }
      Predicate::InSet(elements) => elements.contains(arg),
      Predicate::And(p, q) => p.denote(arg) && q.denote(arg),
      Predicate::Or(p, q) => p.denote(arg) || q.denote(arg),
      Predicate::Not(p) => !p.denote(arg),
      Predicate::WithLambda { p, f } => p.denote(f.apply(arg)),
    }
  }

  fn satisfiable(&self) -> bool {
    matches!(self, Predicate::Bool(false))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn char() {
    let eq_a = Predicate::char('a');
    assert_eq!(Predicate::Eq('a'), eq_a);

    assert!(eq_a.denote(&'a'));
    assert!(!eq_a.denote(&'b'));
  }

  #[test]
  fn range() {
    let b = &'b';
    let f = &'f';
    let z = &'z';

    let bigger_than_c = Predicate::range(Some('c'), None);
    assert_eq!(
      Predicate::Range {
        left: Some('c'),
        right: None
      },
      bigger_than_c
    );
    let bigger_than_c = bigger_than_c;
    assert!(!bigger_than_c.denote(b));
    assert!(bigger_than_c.denote(f));
    assert!(bigger_than_c.denote(z));

    let smaller_than_v = Predicate::range(None, Some('v'));
    assert_eq!(
      Predicate::Range {
        left: None,
        right: Some('v')
      },
      smaller_than_v
    );
    let smaller_than_v = smaller_than_v;
    assert!(smaller_than_v.denote(b));
    assert!(smaller_than_v.denote(f));
    assert!(!smaller_than_v.denote(z));

    let between_f_k = Predicate::range(Some('f'), Some('k'));
    assert_eq!(
      Predicate::Range {
        left: Some('f'),
        right: Some('k')
      },
      between_f_k
    );
    let between_f_k = between_f_k;
    assert!(!between_f_k.denote(b));
    assert!(between_f_k.denote(f));
    assert!(between_f_k.denote(&'i'));
    assert!(!between_f_k.denote(z));

    let top = Predicate::range(None, None);
    assert_eq!(Predicate::Bool(true), top);
    let top = top;
    assert!(top.denote(b));
    assert!(top.denote(f));
    assert!(top.denote(z));

    let err = Predicate::range(Some('k'), Some('f'));
    assert_eq!(Predicate::Bool(false), err);
    let bot = err;
    assert!(!bot.denote(b));
    assert!(!bot.denote(f));
    assert!(!bot.denote(z));

    let eq = Predicate::range(Some('f'), Some('f'));
    assert_eq!(Predicate::Eq('f'), eq);
    let eq = eq;
    assert!(!eq.denote(b));
    assert!(eq.denote(f));
    assert!(!eq.denote(z));
  }

  #[test]
  fn in_set() {
    let avd = Predicate::in_set(&['a', 'v', 'd']);
    assert_eq!(Predicate::InSet(vec!['a', 'v', 'd']), avd);

    assert!(avd.denote(&'a'));
    assert!(avd.denote(&'v'));
    assert!(avd.denote(&'d'));
    assert!(!avd.denote(&'c'));
    assert!(!avd.denote(&'h'));
    assert!(!avd.denote(&'i'));
  }

  #[test]
  fn with_lambda() {
    let cond_x = Predicate::char('x');
    let cond_num = Predicate::range(Some('0'), Some('9'));
    let cond_set_xyz = Predicate::in_set(&['x', 'y', 'z']);

    let cnst;
    let map;
    let fnc;
    {
      let fnc_cond1 = Predicate::range(Some('f'), Some('l')); //f, g, h, i, j, k
      let fnc_cond2 = Predicate::in_set(&['b', 's', 'w']);

      cnst = Lambda::<Predicate<char>>::Constant('x');
      map = Lambda::<Predicate<char>>::Mapping(vec![('a', 'x'), ('b', 'y'), ('c', 'z')]);
      fnc = Lambda::<Predicate<char>>::Function(vec![
        (Box::new(fnc_cond1), '1'),
        (Box::new(fnc_cond2), '2'),
      ]);
    }

    let cond_x = cond_x.with_lambda(cnst);
    assert!(cond_x.denote(&'a'));
    assert!(cond_x.denote(&'x'));
    assert!(cond_x.denote(&'z'));
    assert!(cond_x.denote(&'9'));

    let cond_set_xyz = cond_set_xyz.with_lambda(map);
    assert!(cond_set_xyz.denote(&'a'));
    assert!(cond_set_xyz.denote(&'b'));
    assert!(cond_set_xyz.denote(&'c'));
    assert!(!cond_set_xyz.denote(&'0'));
    assert!(!cond_set_xyz.denote(&'s'));

    let cond_num = cond_num.with_lambda(fnc);
    assert!(cond_num.denote(&'f'));
    assert!(cond_num.denote(&'g'));
    assert!(cond_num.denote(&'h'));
    assert!(cond_num.denote(&'i'));
    assert!(cond_num.denote(&'k'));
    assert!(!cond_num.denote(&'l'));

    assert!(cond_num.denote(&'b'));
    assert!(cond_num.denote(&'s'));
    assert!(cond_num.denote(&'w'));
    assert!(!cond_num.denote(&'p'));
    assert!(!cond_num.denote(&'a'));
  }
}
