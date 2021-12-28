use crate::boolean_algebra::{BoolAlg, Predicate};
use std::{
  fmt::Debug,
  hash::Hash,
  rc::Rc,
  sync::atomic::{AtomicUsize, Ordering},
};

pub trait FunctionTerm: Debug + PartialEq + Eq + Hash + Clone {
  type Underlying: BoolAlg;

  fn apply<'a>(
    &'a self,
    arg: &'a <Self::Underlying as BoolAlg>::Domain,
  ) -> &'a <Self::Underlying as BoolAlg>::Domain;

  /** functional composition of self (other (x)) */
  fn compose(self, other: Self) -> Self;

  fn identity() -> Self;
}

/**
 * for Primitive Function Term
 */
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Lambda<T: BoolAlg + ?Sized> {
  Id,
  Constant(T::Domain),
  Mapping(Vec<(T::Domain, T::Domain)>),
  Function(Vec<(Box<T>, T::Domain)>),
}
impl<T: BoolAlg> Lambda<T> {
  pub fn constant(c: T::Domain) -> Lambda<T> {
    Lambda::Constant(c)
  }

  pub fn mapping(m: Vec<(T::Domain, T::Domain)>) -> Lambda<T> {
    Lambda::Mapping(m)
  }
}
impl<T> FunctionTerm for Lambda<T>
where
  T: BoolAlg,
  T::Domain: Clone + Eq,
{
  type Underlying = T;

  fn apply<'a>(
    &'a self,
    arg: &'a <Self::Underlying as BoolAlg>::Domain,
  ) -> &'a <Self::Underlying as BoolAlg>::Domain {
    match self {
      Lambda::Id => arg,
      Lambda::Constant(c) => c,
      Lambda::Mapping(map) => match map.iter().find(|(k, _)| *k == *arg) {
        Some((_, v)) => v,
        None => arg,
      },
      Lambda::Function(f) => match f.iter().find(|(cond, _)| cond.denote(arg)) {
        Some((_, value)) => value,
        None => arg,
      },
    }
  }

  fn compose(self, other: Self) -> Self {
    match (&self, &other) {
      (_, Lambda::Id) => self,
      (Lambda::Id, _) => other,
      (Lambda::Constant(_), _) => self,
      (f, Lambda::Constant(c)) => Lambda::Constant(f.apply(c).clone()),
      (f, Lambda::Mapping(map)) => Lambda::Mapping(
        map
          .into_iter()
          .map(|(k, v)| (k.clone(), f.apply(v).clone()))
          .collect(),
      ),
      (f, Lambda::Function(g)) => Lambda::Function(
        g.into_iter()
          .map(|(phi, val)| (phi.clone(), f.apply(val).clone()))
          .collect(),
      ),
    }
  }

  fn identity() -> Self {
    Lambda::Id
  }
}

static VAR_CNT: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct VariableImpl(usize);
impl VariableImpl {
  pub fn new() -> VariableImpl {
    VariableImpl(VAR_CNT.fetch_add(1, Ordering::SeqCst))
  }
}

pub trait Variable: Debug + Eq + Hash + Clone {
  fn new() -> Self;
}
impl Variable for VariableImpl {
  fn new() -> Self {
    VariableImpl::new()
  }
}
impl Variable for Rc<VariableImpl> {
  fn new() -> Self {
    Rc::new(VariableImpl::new())
  }
}

#[derive(Debug, PartialEq, Clone)]
pub enum UpdateComp<T: FunctionTerm, V: Variable> {
  F(T),
  X(V),
}

#[derive(Debug, PartialEq, Clone)]
pub enum OutputComp<T, V: Variable> {
  A(T),
  X(V),
}

pub type FunctionTermImpl<T> = Lambda<Predicate<T>>;

#[cfg(test)]
pub mod tests {
  use super::*;
  use std::collections::{
    hash_map::{DefaultHasher, RandomState},
    HashSet,
  };
  use std::hash::Hasher;
  use std::iter::FromIterator;

  #[test]
  fn new_var_is_new() {
    let var_1 = VariableImpl::new();
    let var_2 = VariableImpl::new();

    assert_eq!(var_1, var_1);
    assert_ne!(var_1, var_2);
    assert_eq!(var_2, var_2);
    assert_ne!(var_2, var_1);
  }

  #[test]
  fn var_distingish_from_another() {
    fn new() -> VariableImpl {
      Variable::new()
    }
    let v1 = new();
    let v2 = new();
    let v3 = v1.clone();

    assert_ne!(v1, v2);
    assert!(v1 == v3 && v1.0 == v3.0);

    let v1_hash = {
      let mut hasher = DefaultHasher::new();
      v1.hash(&mut hasher);
      hasher.finish()
    };
    let v2_hash = {
      let mut hasher = DefaultHasher::new();
      v2.hash(&mut hasher);
      hasher.finish()
    };
    let v3_hash = {
      let mut hasher = DefaultHasher::new();
      v3.hash(&mut hasher);
      hasher.finish()
    };

    assert_ne!(v1_hash, v2_hash);
    assert_eq!(v1_hash, v3_hash);

    let mut vars100 = HashSet::with_hasher(RandomState::new());
    for _ in 0..100 {
      vars100.insert(new());
    }

    let v = new();
    let var1 = vec![v; 100];
    let var1 = HashSet::<_, RandomState>::from_iter(var1.iter());

    assert_eq!(vars100.len(), 100);
    assert_eq!(var1.len(), 1);
  }
}
