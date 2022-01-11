use crate::boolean_algebra::{BoolAlg, Predicate};
use crate::util::Domain;
use std::{
  fmt::Debug,
  hash::Hash,
  rc::Rc,
  sync::atomic::{AtomicUsize, Ordering},
};

pub trait FunctionTerm: Debug + Eq + Hash + Clone {
  type Domain: Domain;

  fn identity() -> Self;

  fn constant(a: Self::Domain) -> Self;

  fn separator() -> Self {
    Self::constant(Self::Domain::separator())
  }

  fn apply<'a>(&'a self, arg: &'a Self::Domain) -> &'a Self::Domain;

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
  pub fn mapping(m: Vec<(B::Domain, B::Domain)>) -> Lambda<B> {
    Lambda::Mapping(m)
  }
}
impl<B> FunctionTerm for Lambda<B>
where
  B: BoolAlg,
  B::Domain: Domain,
{
  type Domain = B::Domain;

  fn identity() -> Self {
    Lambda::Id
  }

  fn constant(a: Self::Domain) -> Self {
    Lambda::Constant(a)
  }

  fn apply<'a>(&'a self, arg: &'a Self::Domain) -> &'a Self::Domain {
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

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct VariableImpl(usize);
impl VariableImpl {
  pub fn new() -> VariableImpl {
    VariableImpl(VAR_CNT.fetch_add(1, Ordering::SeqCst))
  }
}
impl Debug for VariableImpl {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.write_fmt(format_args!("X({})", self.0))
  }
}

#[derive(PartialEq, Clone)]
pub enum UpdateComp<F: FunctionTerm, V: Variable> {
  /** function term representation */
  F(F),
  /** variable representation */
  X(V),
}
impl<F: FunctionTerm, V: Variable> Debug for UpdateComp<F, V> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::F(lambda) => f.write_fmt(format_args!("{:?}", lambda)),
      Self::X(var) => f.write_fmt(format_args!("{:?}", var)),
    }
  }
}
impl<D: Domain, V: Variable, F: FunctionTerm<Domain = D>> From<OutputComp<D, V>>
  for UpdateComp<F, V>
{
  fn from(component: OutputComp<D, V>) -> Self {
    match component {
      OutputComp::A(a) => UpdateComp::F(F::constant(a)),
      OutputComp::X(x) => UpdateComp::X(x),
    }
  }
}
#[derive(PartialEq, Clone)]
pub enum OutputComp<D: Domain, V: Variable> {
  /** domain character representation */
  A(D),
  /** variable representation */
  X(V),
}
impl<D: Domain, V: Variable> Debug for OutputComp<D, V> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::A(a) => f.write_fmt(format_args!("{:?}", a)),
      Self::X(var) => f.write_fmt(format_args!("{:?}", var)),
    }
  }
}

pub type FunctionTermImpl<T> = Lambda<Predicate<T>>;

#[cfg(test)]
mod tests {
  use super::*;
  use std::{
    collections::{
      hash_map::{DefaultHasher, RandomState},
      HashSet,
    },
    hash::Hasher,
    iter::FromIterator
  };

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
