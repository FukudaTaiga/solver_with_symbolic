use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::util::FromChar;
use std::{
  fmt::Debug,
  hash::Hash,
  rc::Rc,
  sync::atomic::{AtomicUsize, Ordering},
};

pub trait FunctionTerm: Debug + Eq + Hash + Clone {
  type Domain: FromChar;

  fn identity() -> Self;

  fn apply<'a>(
    &'a self,
    arg: &'a Self::Domain,
  ) -> &'a Self::Domain;

  /** functional composition of self (other (x)) */
  fn compose(self, other: Self) -> Self;
}

/** for Primitive Function Term */
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Lambda<B: BoolAlg + ?Sized> {
  Id,
  Constant(B::Domain),
  Mapping(Vec<(B::Domain, B::Domain)>),
  Function(Vec<(Box<B>, B::Domain)>),
}
impl<B: BoolAlg> Lambda<B> {
  pub fn constant(c: B::Domain) -> Lambda<B> {
    Lambda::Constant(c)
  }

  pub fn mapping(m: Vec<(B::Domain, B::Domain)>) -> Lambda<B> {
    Lambda::Mapping(m)
  }
}
impl<B> FunctionTerm for Lambda<B>
where
  B: BoolAlg,
  B::Domain: Clone + Eq,
{
  type Domain = B::Domain;

  fn identity() -> Self {
    Lambda::Id
  }

  fn apply<'a>(
    &'a self,
    arg: &'a Self::Domain,
  ) -> &'a Self::Domain {
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
}

pub trait Variable: Debug + Eq + Ord + Hash + Clone {
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

static VAR_CNT: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct VariableImpl(usize);
impl VariableImpl {
  pub fn new() -> VariableImpl {
    VariableImpl(VAR_CNT.fetch_add(1, Ordering::SeqCst))
  }
}

#[derive(Debug, PartialEq, Clone)]
pub enum UpdateComp<F: FunctionTerm, V: Variable> {
  F(F),
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
