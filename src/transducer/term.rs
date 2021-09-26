#![allow(dead_code)]
use crate::boolean_algebra::BoolAlg;
use std::borrow::Borrow;
use std::hash::Hash;
use std::rc::Rc;

pub trait FunctionTerm {
    type Underlying: BoolAlg;

    fn apply<'a>(
        &'a self,
        arg: &'a <Self::Underlying as BoolAlg>::Domain,
    ) -> &'a <Self::Underlying as BoolAlg>::Domain;

    fn compose(self: &Rc<Self>, other: &Rc<Self>) -> Rc<Self>;

    fn identity() -> Self;
}

/**
 * for Primitive Function Term
 */
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Lambda<T: BoolAlg> {
    Id,
    Constant(T::Domain),
    Mapping(Vec<(T::Domain, T::Domain)>),
    Function(Vec<(Rc<T>, T::Domain)>),
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
    T::Domain: Copy + Eq,
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
            Lambda::Function(f) => match f.iter().find(|(cond, _)| cond.denotate(arg)) {
                Some((_, value)) => value,
                None => arg,
            },
        }
    }

    fn compose(self: &Rc<Self>, other: &Rc<Self>) -> Rc<Self> {
        match (self.borrow(), other.borrow()) {
            (Lambda::Id, _) => Rc::clone(other),
            (_, Lambda::Id) => Rc::clone(self),
            (_, Lambda::Constant(_)) => Rc::clone(other),
            (Lambda::Constant(c), g) => Rc::new(Lambda::Constant(*g.apply(&c))),
            (Lambda::Mapping(map), g) => Rc::new(Lambda::Mapping(
                map.into_iter().map(|(k, v)| (*k, *g.apply(v))).collect(),
            )),
            (Lambda::Function(f), g) => Rc::new(Lambda::Function(
                f.into_iter()
                    .map(|(phi, v)| (Rc::clone(phi), *g.apply(v)))
                    .collect(),
            )),
        }
    }

    fn identity() -> Self {
        Lambda::Id
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Variable<'a>(&'a str);
impl Variable<'_> {
    pub fn new(name: &str) -> Variable<'_> {
        Variable(name)
    }
}

#[derive(Debug)]
pub enum UpdateComp<'a, T: FunctionTerm> {
    F(T),
    X(Rc<Variable<'a>>),
}

#[derive(Debug)]
pub enum OutputComp<'a, T> {
    A(T),
    X(Rc<Variable<'a>>),
}
