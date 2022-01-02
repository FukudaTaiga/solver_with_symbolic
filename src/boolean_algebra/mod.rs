use crate::transducer::term::{FunctionTerm, Lambda};
use crate::util::Domain;
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
pub trait BoolAlg: Debug + Eq + Hash + Clone {
  type Domain: Domain;
  type Term: FunctionTerm<Domain = Self::Domain>;

  /**
   * predicate that equals x == a.
   * it names `char` because
   * `eq` is already defined in trait PartialEq
   * and the name like it is confusing.
   */
  fn char(a: Self::Domain) -> Self;
  fn and(&self, other: &Self) -> Self;
  fn or(&self, other: &Self) -> Self;
  fn not(&self) -> Self;
  fn top() -> Self;
  fn bot() -> Self;
  fn with_lambda(&self, f: &Self::Term) -> Self;

  fn all_char() -> Self {
    //Self::char(Self::Domain::separator()).not()
    Self::top()
  }

  fn boolean(b: bool) -> Self {
    if b {
      Self::top()
    } else {
      Self::bot()
    }
  }

  /** apply argument to self and return the result */
  fn denote(&self, arg: &Self::Domain) -> bool;

  fn satisfiable(&self) -> bool;
}
/** Boolean Algebra with epsilon */
impl<B: BoolAlg> BoolAlg for Option<B> {
  type Domain = B::Domain;
  type Term = B::Term;

  fn char(a: Self::Domain) -> Self {
    Some(B::char(a))
  }
  fn and(&self, other: &Self) -> Self {
    self
      .as_ref()
      .and_then(|p1| other.as_ref().map(|p2| p1.and(p2)))
      .or(Some(B::bot()))
  }
  fn or(&self, other: &Self) -> Self {
    self
      .as_ref()
      .and_then(|p1| other.as_ref().map(|p2| p1.or(p2)))
      .or(Some(B::bot()))
  }
  fn not(&self) -> Self {
    self.as_ref().map(|p| p.not())
  }
  fn top() -> Self {
    Some(B::top())
  }
  fn bot() -> Self {
    Some(B::bot())
  }
  fn with_lambda(&self, f: &Self::Term) -> Self {
    self.as_ref().map(|p| p.with_lambda(f))
  }

  fn denote(&self, arg: &Self::Domain) -> bool {
    self.as_ref().map_or_else(|| true, |p| p.denote(arg))
  }

  fn satisfiable(&self) -> bool {
    self.as_ref().map_or_else(|| true, |p| p.satisfiable())
  }
}

/** for Primitive Predicate */
#[derive(Debug, Eq, Hash, Clone)]
pub enum Predicate<T: Domain> {
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
impl<T: Domain> PartialEq for Predicate<T> {
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
impl<T: Domain> Predicate<T> {
  pub fn range(left: Option<T>, right: Option<T>) -> Self {
    match (left.as_ref(), right.as_ref()) {
      (Some(l), Some(r)) => {
        if *r < *l {
          Predicate::bot()
        } else if *r == *l {
          Predicate::char(left.unwrap())
        } else {
          Predicate::Range { left, right }
        }
      }
      (None, None) => Predicate::top(),
      _ => Predicate::Range { left, right },
    }
  }

  pub fn in_set(elements: impl IntoIterator<Item = T>) -> Self {
    let mut elements = elements.into_iter();
    let mut els = vec![];

    while let Some(e) = elements.next() {
      if !els.contains(&e) {
        els.push(e);
      }
    }

    els.sort();

    if els.len() == 0 {
      Predicate::bot()
    } else if els.len() == 1 {
      Predicate::char(els.pop().unwrap())
    } else {
      Predicate::InSet(els)
    }
  }
}
impl<T: Domain> BoolAlg for Predicate<T> {
  type Domain = T;
  type Term = Lambda<Self>;

  fn char(a: Self::Domain) -> Self {
    Predicate::Eq(a)
  }

  fn and(&self, other: &Self) -> Self {
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
        let pl = pl.as_ref();
        let ql = ql.as_ref();
        let pr = pr.as_ref();
        let qr = qr.as_ref();

        let left = pl.map_or_else(
          || ql,
          |pl| ql.map_or_else(|| Some(pl), |ql| Some(pl.max(ql))),
        );
        let right = pr.map_or_else(
          || qr,
          |pr| qr.map_or_else(|| Some(pr), |qr| Some(pr.min(qr))),
        );

        Predicate::range(left.cloned(), right.cloned())
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
          Predicate::in_set(els_)
        }
      }
      (Predicate::Not(p), q) | (q, Predicate::Not(p)) if **p == *q => Predicate::bot(),
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

  fn or(&self, other: &Self) -> Self {
    match (self, other) {
      (Predicate::Bool(b), p) | (p, Predicate::Bool(b)) => {
        if *b {
          Predicate::top()
        } else {
          p.clone()
        }
      }
      (Predicate::Eq(c), p) | (p, Predicate::Eq(c)) if p.denote(c) => p.clone(),
      (Predicate::Eq(c1), Predicate::Eq(c2)) => Predicate::in_set([c1.clone(), c2.clone()]),
      (Predicate::Eq(c), Predicate::InSet(els)) | (Predicate::InSet(els), Predicate::Eq(c)) => {
        let mut els_ = els.clone();
        els_.push(c.clone());
        Predicate::in_set(els_)
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
        if matches!((pl, qr), (Some(l), Some(r)) if l <= r)
          || matches!((ql, pr), (Some(l), Some(r)) if l <= r)
        {
          let pl = pl.as_ref();
          let ql = ql.as_ref();
          let pr = pr.as_ref();
          let qr = qr.as_ref();

          let left = pl.and_then(|pl| ql.map(|ql| pl.min(ql)));
          let right = pr.and_then(|pr| qr.map(|qr| pr.max(qr)));
          Predicate::range(left.cloned(), right.cloned())
        } else {
          Predicate::Or(Box::new(self.clone()), Box::new(other.clone()))
        }
      }
      (Predicate::InSet(els1), Predicate::InSet(els2)) => {
        let els: std::collections::HashSet<_> = els1.into_iter().chain(els2.into_iter()).collect();
        Predicate::in_set(els.into_iter().cloned())
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
          Predicate::Or(Box::new(Predicate::in_set(els_)), Box::new(p.clone()))
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

  fn with_lambda(&self, f: &Self::Term) -> Self {
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
          f: f.clone().compose(f2.clone()),
        },
        _ => Predicate::WithLambda {
          p: Box::new(self.clone()),
          f: f.clone(),
        },
      },
    }
  }

  fn denote(&self, arg: &Self::Domain) -> bool {
    match self {
      Predicate::Bool(b) => *b,
      Predicate::Eq(a) => *a == *arg,
      Predicate::Range { left, right } => {
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
    !matches!(self, Predicate::Bool(false))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  type Prd = Predicate<char>;

  #[test]
  fn char() {
    let eq_a = Prd::char('a');
    assert_eq!(Prd::Eq('a'), eq_a);

    assert!(eq_a.denote(&'a'));
    assert!(!eq_a.denote(&'b'));
  }

  #[test]
  fn range() {
    let b = &'b';
    let f = &'f';
    let z = &'z';

    let bigger_than_c = Prd::range(Some('c'), None);
    assert_eq!(
      Prd::Range {
        left: Some('c'),
        right: None
      },
      bigger_than_c
    );
    let bigger_than_c = bigger_than_c;
    assert!(!bigger_than_c.denote(b));
    assert!(bigger_than_c.denote(f));
    assert!(bigger_than_c.denote(z));

    let smaller_than_v = Prd::range(None, Some('v'));
    assert_eq!(
      Prd::Range {
        left: None,
        right: Some('v')
      },
      smaller_than_v
    );
    let smaller_than_v = smaller_than_v;
    assert!(smaller_than_v.denote(b));
    assert!(smaller_than_v.denote(f));
    assert!(!smaller_than_v.denote(z));

    let between_f_k = Prd::range(Some('f'), Some('k'));
    assert_eq!(
      Prd::Range {
        left: Some('f'),
        right: Some('k')
      },
      between_f_k
    );
    let between_f_k = between_f_k;
    assert!(!between_f_k.denote(b));
    assert!(between_f_k.denote(f));
    assert!(between_f_k.denote(&'i'));
    assert!(!between_f_k.denote(&'k'));
    assert!(!between_f_k.denote(z));

    let top = Prd::range(None, None);
    assert_eq!(Prd::Bool(true), top);
    let top = top;
    assert!(top.denote(b));
    assert!(top.denote(f));
    assert!(top.denote(z));

    let err = Prd::range(Some('k'), Some('f'));
    assert_eq!(Prd::Bool(false), err);
    let bot = err;
    assert!(!bot.denote(b));
    assert!(!bot.denote(f));
    assert!(!bot.denote(z));

    let eq = Prd::range(Some('f'), Some('f'));
    assert_eq!(Prd::Eq('f'), eq);
    let eq = eq;
    assert!(!eq.denote(b));
    assert!(eq.denote(f));
    assert!(!eq.denote(z));
  }

  #[test]
  fn in_set() {
    let avd = Prd::in_set(['a', 'v', 'd']);
    assert_eq!(Prd::InSet(vec!['a', 'd', 'v']), avd);

    assert!(avd.denote(&'a'));
    assert!(avd.denote(&'v'));
    assert!(avd.denote(&'d'));
    assert!(!avd.denote(&'c'));
    assert!(!avd.denote(&'h'));
    assert!(!avd.denote(&'i'));
  }

  #[test]
  fn with_lambda() {
    let cond_x = Prd::char('x');
    let cond_num = Prd::range(Some('0'), Some('9'));
    let cond_set_xyz = Prd::in_set(['x', 'y', 'z']);

    let cond_x = cond_x.with_lambda(&Lambda::Constant('x'));
    assert!(cond_x.denote(&'a'));
    assert!(cond_x.denote(&'x'));
    assert!(cond_x.denote(&'z'));
    assert!(cond_x.denote(&'9'));

    let cond_set_xyz =
      cond_set_xyz.with_lambda(&Lambda::Mapping(vec![('a', 'x'), ('b', 'y'), ('c', 'z')]));
    assert!(cond_set_xyz.denote(&'a'));
    assert!(cond_set_xyz.denote(&'b'));
    assert!(cond_set_xyz.denote(&'c'));
    assert!(!cond_set_xyz.denote(&'0'));
    assert!(!cond_set_xyz.denote(&'s'));

    let fnc_cond1 = Prd::range(Some('f'), Some('l')); //f, g, h, i, j, k
    let fnc_cond2 = Prd::in_set(['b', 's', 'w']);

    let cond_num = cond_num.with_lambda(&Lambda::Function(vec![
      (Box::new(fnc_cond1), '1'),
      (Box::new(fnc_cond2), '2'),
    ]));
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
