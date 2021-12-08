use crate::char_util::FromChar;
use crate::transducer::term::{FunctionTerm, Lambda};
use std::{fmt::Debug, hash::Hash, rc::Rc};

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
  type Domain: FromChar;

  fn and(self: &Rc<Self>, other: &Rc<Self>) -> Rc<Self>;
  fn or(self: &Rc<Self>, other: &Rc<Self>) -> Rc<Self>;
  fn not(self: &Rc<Self>) -> Rc<Self>;
  fn top() -> Rc<Self>;
  fn bot() -> Rc<Self>;

  /** apply argument to self and return the result */
  fn denotate(&self, arg: &Self::Domain) -> bool;

  fn is_bottom(&self) -> bool;
}

/**
 * for Primitive Predicate
 */
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Predicate<T: FromChar> {
  Bool(bool),
  Eq(T),
  Range {
    /** whether satisfying arg left <= arg && arg < right */
    left: Option<T>,
    right: Option<T>,
  },
  InSet(Vec<T>),
  And(Rc<Self>, Rc<Self>),
  Or(Rc<Self>, Rc<Self>),
  Not(Rc<Self>),
  WithLambda {
    p: Rc<Self>,
    f: Rc<Lambda<Self>>,
  },
}
impl<T: FromChar> Predicate<T> {
  pub fn eq(a: T) -> Rc<Self> {
    Rc::new(Predicate::Eq(a))
  }

  pub fn range(left: Option<T>, right: Option<T>) -> Rc<Self> {
    match (&left, &right) {
      (Some(l), Some(r)) => {
        if *r < *l {
          Predicate::bot()
        } else if *r == *l {
          Predicate::eq(l.clone())
        } else {
          Rc::new(Predicate::Range { left, right })
        }
      }
      (None, None) => Predicate::top(),
      _ => Rc::new(Predicate::Range { left, right }),
    }
  }

  pub fn in_set(elements: &[T]) -> Rc<Self> {
    if elements.len() == 0 {
      Predicate::bot()
    } else if elements.len() == 1 {
      Predicate::eq(elements[0].clone())
    } else {
      Rc::new(Predicate::InSet(Vec::from(elements)))
    }
  }

  pub fn with_lambda(self: Rc<Self>, f: Rc<Lambda<Self>>) -> Rc<Self> {
    Rc::new(Predicate::WithLambda { p: self, f })
  }

  /**
   * if any children formulas have been reduced, there is no need to reduce recursively
   */
  fn reduce(self) -> Rc<Self> {
    match self {
      Predicate::And(ref p, ref q) => match (&**p, &**q) {
        /* able to determine the value at creating */
        (Predicate::Bool(b), _) => {
          if *b {
            Rc::clone(q)
          } else {
            Rc::clone(p)
          }
        }
        (_, Predicate::Bool(b)) => {
          if *b {
            Rc::clone(p)
          } else {
            Rc::clone(q)
          }
        }
        /* p or q is Eq predicate */
        (Predicate::Eq(ref e), q) => {
          if q.denotate(e) {
            Rc::clone(p)
          } else {
            Predicate::bot()
          }
        }
        (p, Predicate::Eq(ref e)) => {
          if p.denotate(e) {
            Rc::clone(q)
          } else {
            Predicate::bot()
          }
        }
        /* p or q is Range predicate */
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
            /* q is of the form |ql\_______/qr| */
            (Some(pl), Some(pr), Some(ql), Some(qr)) if *ql <= *pr && *pl <= *qr => {
              if *ql < *pl {
                if *qr < *pr {
                  /* ql\__pl\_result_/qr__/pr */
                  Predicate::range(Some(pl.clone()), Some(qr.clone()))
                } else {
                  /* ql\__pl\_result_/pr__qr */
                  Rc::clone(p)
                }
              } else {
                if *qr <= *pr {
                  /* pl\__ql\_result_/qr__/pr */
                  Rc::clone(q)
                } else {
                  /* pl\__ql\_result_/pr__/qr */
                  Predicate::range(Some(ql.clone()), Some(pr.clone()))
                }
              }
            }
            (Some(pl), None, Some(ql), Some(qr)) if *pl <= *qr => {
              if *pl <= *ql {
                Rc::clone(q)
              } else {
                Predicate::range(Some(pl.clone()), Some(qr.clone()))
              }
            }
            (None, Some(pr), Some(ql), Some(qr)) if *ql <= *pr => {
              if *qr <= *pr {
                Rc::clone(q)
              } else {
                Predicate::range(Some(ql.clone()), Some(pr.clone()))
              }
            }
            /* q is of the form |_______/qr| */
            (Some(pl), Some(pr), None, Some(qr)) if *pl <= *qr => {
              if *pr <= *qr {
                Rc::clone(p)
              } else {
                Predicate::range(Some(pl.clone()), Some(qr.clone()))
              }
            }
            (Some(pl), None, None, Some(qr)) => {
              Predicate::range(Some(pl.clone()), Some(qr.clone()))
            }
            (None, Some(pr), None, Some(qr)) => {
              if *qr <= *pr {
                Rc::clone(q)
              } else {
                Rc::clone(p)
              }
            }
            /* q is of the form |ql\_______| */
            (Some(pl), Some(pr), Some(ql), None) if *ql <= *pr => {
              if *ql <= *pl {
                Rc::clone(p)
              } else {
                Predicate::range(Some(ql.clone()), Some(pr.clone()))
              }
            }
            (Some(pl), None, Some(ql), None) => {
              if *pl <= *ql {
                Rc::clone(q)
              } else {
                Rc::clone(p)
              }
            }
            (None, Some(pr), Some(ql), None) => {
              Predicate::range(Some(ql.clone()), Some(pr.clone()))
            }
            _ => Predicate::bot(),
          }
        }
        (Predicate::InSet(ref els), _) => {
          let els_ = els
            .into_iter()
            .filter_map(|e| if p.denotate(e) { Some(e.clone()) } else { None })
            .collect::<Vec<_>>();
          if els_.len() == els.len() {
            Rc::clone(p)
          } else {
            Predicate::in_set(&els_)
          }
        }
        (_, Predicate::InSet(ref els)) => {
          let els_ = els
            .into_iter()
            .filter_map(|e| if p.denotate(e) { Some(e.clone()) } else { None })
            .collect::<Vec<_>>();
          if els_.len() == els.len() {
            Rc::clone(q)
          } else {
            Predicate::in_set(&els_)
          }
        }
        _ => Rc::new(self),
      },
      Predicate::Or(ref p, ref q) => match (&**p, &**q) {
        /* able to determine the value at creating */
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
        /* p or q is Eq predicate */
        (Predicate::Eq(ref e), _) => {
          if q.denotate(e) {
            Rc::clone(q)
          } else {
            Rc::new(self)
          }
        }
        (_, Predicate::Eq(ref e)) => {
          if p.denotate(e) {
            Rc::clone(p)
          } else {
            Rc::new(self)
          }
        }
        /* p or q is Range predicate */
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
          /* reduce if one range surrounds other. */
          match (pl, pr, ql, qr) {
            /* q is of the form |ql\_______/qr| */
            (Some(pl), Some(pr), Some(ql), Some(qr)) if *ql <= *pr && *pl <= *qr => {
              if *ql <= *pl {
                if *pr <= *qr {
                  /* ql\__pl\______/pr__/qr */
                  Rc::clone(q)
                } else {
                  /* ql\__pl\_______/qr__/pr */
                  Predicate::range(Some(ql.clone()), Some(pr.clone()))
                }
              } else {
                if *qr <= *pr {
                  /* pl\__ql\_______/qr__/pr */
                  Rc::clone(p)
                } else {
                  /* pl\__ql\______/pr__/qr */
                  Predicate::range(Some(pl.clone()), Some(qr.clone()))
                }
              }
            }
            (Some(pl), None, Some(ql), Some(qr)) if *pl <= *qr => {
              if *pl <= *ql {
                Rc::clone(p)
              } else {
                Predicate::range(Some(ql.clone()), None)
              }
            }
            (None, Some(pr), Some(ql), Some(qr)) if *ql <= *pr => {
              if *qr <= *pr {
                Rc::clone(p)
              } else {
                Predicate::range(None, Some(qr.clone()))
              }
            }
            /* q is of the form |_______/qr| */
            (Some(pl), Some(pr), None, Some(qr)) if *pl <= *qr => {
              if *pr <= *qr {
                Rc::clone(q)
              } else {
                Predicate::range(None, Some(pr.clone()))
              }
            }
            (Some(pl), None, None, Some(qr)) if *pl <= *qr => Predicate::top(),
            (None, Some(pr), None, Some(qr)) => {
              if *qr <= *pr {
                Rc::clone(p)
              } else {
                Rc::clone(q)
              }
            }
            /* q is of the form |ql\_______| */
            (Some(pl), Some(pr), Some(ql), None) if *ql <= *pr => {
              if *ql <= *pl {
                Rc::clone(q)
              } else {
                Predicate::range(Some(pl.clone()), None)
              }
            }
            (Some(pl), None, Some(ql), None) => {
              if *pl <= *ql {
                Rc::clone(p)
              } else {
                Rc::clone(q)
              }
            }
            (None, Some(pr), Some(ql), None) if *ql <= *pr => Predicate::top(),
            _ => Rc::new(self),
          }
        }
        (Predicate::InSet(ref els), _) => {
          let els_ = els
            .into_iter()
            .filter(|e| p.denotate(*e))
            .collect::<Vec<_>>();
          if els_.len() == els.len() {
            Rc::clone(q)
          } else {
            Rc::new(self)
          }
        }
        (_, Predicate::InSet(ref els)) => {
          let els_ = els
            .into_iter()
            .filter(|e| p.denotate(*e))
            .collect::<Vec<_>>();
          if els_.len() == els.len() {
            Rc::clone(p)
          } else {
            Rc::new(self)
          }
        }
        _ => Rc::new(self),
      },
      Predicate::Not(ref p) => match **p {
        Predicate::Bool(b) => Rc::new(Predicate::Bool(!b)),
        _ => Rc::new(self),
      },
      _ => Rc::new(self),
    }
  }
}
impl<T: FromChar> BoolAlg for Predicate<T> {
  type Domain = T;

  /**
   * TODO -- should be reducible
   * self.reduce() work sometimes but not on other. ??
   */
  fn and(self: &Rc<Self>, other: &Rc<Self>) -> Rc<Self> {
    Predicate::And(Rc::clone(self), Rc::clone(other)).reduce()
  }

  fn or(self: &Rc<Self>, other: &Rc<Self>) -> Rc<Self> {
    Predicate::Or(Rc::clone(self), Rc::clone(other)).reduce()
  }

  fn not(self: &Rc<Self>) -> Rc<Self> {
    Predicate::Not(Rc::clone(self)).reduce()
  }

  fn top() -> Rc<Self> {
    Rc::new(Predicate::Bool(true))
  }

  fn bot() -> Rc<Self> {
    Rc::new(Predicate::Bool(false))
  }

  fn denotate(&self, arg: &Self::Domain) -> bool {
    match self {
      Predicate::Bool(b) => *b && *arg != Self::Domain::separator(),
      Predicate::Eq(a) => *a == *arg,
      Predicate::Range { left, right } => {
        return match left {
          Some(l) => *l <= *arg,
          None => true,
        } && match right {
          Some(r) => *arg < *r,
          None => true,
        }
      }
      Predicate::InSet(elements) => elements.contains(arg),
      Predicate::And(p, q) => p.denotate(arg) && q.denotate(arg),
      Predicate::Or(p, q) => p.denotate(arg) || q.denotate(arg),
      Predicate::Not(p) => !p.denotate(arg),
      Predicate::WithLambda { p, f } => p.denotate(f.apply(arg)),
    }
  }

  fn is_bottom(&self) -> bool {
    match self {
      Predicate::Bool(false) => true,
      _ => false,
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn eq() {
    let eq_a = Predicate::eq('a');
    assert_eq!(Predicate::Eq('a'), *eq_a);

    assert!(eq_a.denotate(&'a'));
    assert!(!eq_a.denotate(&'b'));
  }

  #[test]
  fn range() {
    let arg_b = &'b';
    let arg_f = &'f';
    let arg_z = &'z';

    let bigger_than_c = Predicate::range(Some('c'), None);
    assert_eq!(
      Predicate::Range {
        left: Some('c'),
        right: None
      },
      *bigger_than_c
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
      *smaller_than_v
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
      *between_f_k
    );
    let between_f_k = between_f_k;
    assert!(!between_f_k.denotate(arg_b));
    assert!(between_f_k.denotate(arg_f));
    assert!(between_f_k.denotate(&'i'));
    assert!(!between_f_k.denotate(arg_z));

    let top = Predicate::range(None, None);
    assert_eq!(Predicate::Bool(true), *top);
    let top = top;
    assert!(top.denotate(arg_b));
    assert!(top.denotate(arg_f));
    assert!(top.denotate(arg_z));

    let err = Predicate::range(Some('k'), Some('f'));
    assert_eq!(Predicate::Bool(false), *err);
    let bot = err;
    assert!(!bot.denotate(arg_b));
    assert!(!bot.denotate(arg_f));
    assert!(!bot.denotate(arg_z));

    let eq = Predicate::range(Some('f'), Some('f'));
    assert_eq!(Predicate::Eq('f'), *eq);
    let eq = eq;
    assert!(!eq.denotate(arg_b));
    assert!(eq.denotate(arg_f));
    assert!(!eq.denotate(arg_z));
  }

  #[test]
  fn in_set() {
    let avd = &"avd".chars().collect::<Vec<char>>()[..];
    let avd = Predicate::in_set(avd);
    assert_eq!(Predicate::InSet(vec!['a', 'v', 'd']), *avd);

    assert!(avd.denotate(&'a'));
    assert!(avd.denotate(&'v'));
    assert!(avd.denotate(&'d'));
    assert!(!avd.denotate(&'c'));
    assert!(!avd.denotate(&'h'));
    assert!(!avd.denotate(&'i'));
  }

  #[test]
  fn with_lambda() {
    let cond_x = Predicate::eq('x');
    let cond_num = Predicate::range(Some('0'), Some('9'));
    let cond_set_xyz = Predicate::in_set(&['x', 'y', 'z']);

    let cnst;
    let map;
    let fnc;
    {
      let fnc_cond1 = Predicate::range(Some('f'), Some('l')); //f, g, h, i, j, k
      let fnc_cond2 = Predicate::in_set(&['b', 's', 'w']);

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
