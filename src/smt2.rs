use crate::char_util::FromChar;
use crate::regular::regex::Regex;
use crate::state::State;
use crate::transducer::transducer::Transducer;
use smt2parser::{
  concrete::{Command, Constant, Identifier, QualIdentifier, Sort, Symbol, SyntaxBuilder, Term},
  CommandStream, Numeral,
};
use std::{fmt::Debug, iter::FromIterator};

pub type Variables = Vec<String>;

pub fn get_symbol(qi: &QualIdentifier) -> &str {
  if let QualIdentifier::Simple {
    identifier: Identifier::Simple { symbol: Symbol(s) },
  } = qi
  {
    s
  } else {
    panic!("Unsupported: {}", qi);
  }
}

fn get_var_from_str(target: &str, vars: &Variables) -> VarIndex {
  if let Some(idx) = vars.iter().position(|s| s == target) {
    idx
  } else {
    panic!("Variable not found")
  }
}

fn get_var(qi: &QualIdentifier, vars: &Variables) -> VarIndex {
  get_var_from_str(&get_symbol(qi), vars)
}

#[derive(Debug, PartialEq, Clone)]
pub struct LinearTerm {
  var: Option<usize>,
  coefficient: Numeral,
}

#[derive(Debug, PartialEq, Clone)]
pub enum ReplaceTarget {
  Str(String),
  Var(VarIndex),
}
impl ReplaceTarget {
  fn from(term: &Term, vars: &Variables) -> Self {
    match term {
      Term::Constant(Constant::String(s)) => ReplaceTarget::Str(s.clone()),
      Term::QualIdentifier(qi) => ReplaceTarget::Var(get_var(qi, vars)),
      _ => panic!("Unexpected Input"),
    }
  }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TransductionOp<T: FromChar, S: State> {
  Var(VarIndex),
  Reverse(VarIndex),
  Str(String),
  Replace(VarIndex, Regex<T>, ReplaceTarget),
  ReplaceAll(VarIndex, Regex<T>, ReplaceTarget),
  #[allow(dead_code)]
  UserDef(Transducer<T, S>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Transduction<T: FromChar, S: State>(pub Vec<TransductionOp<T, S>>);
impl<T: FromChar, S: State> Transduction<T, S> {
  pub fn empty() -> Self {
    Self(vec![])
  }

  pub fn from(term: &Term, vars: &Variables) -> Self {
    match term {
      Term::QualIdentifier(qi) => Transduction(vec![TransductionOp::Var(get_var(qi, vars))]),
      Term::Constant(Constant::String(s)) => Transduction(vec![TransductionOp::Str(s.clone())]),
      Term::Application {
        qual_identifier,
        arguments,
      } => {
        let op = get_symbol(qual_identifier);
        match &op[..] {
          "str.++" => Transduction(arguments.iter().fold(Vec::new(), |mut res, term| {
            res.extend(Transduction::from(term, vars).0);
            res
          })),
          "str.replaceallre" => {
            if let [var, old, new] = &arguments[..] {
              if let Term::QualIdentifier(qi) = var {
                Transduction(vec![TransductionOp::ReplaceAll(
                  get_var(qi, vars),
                  Regex::new(old),
                  ReplaceTarget::from(new, vars),
                )])
              } else {
                panic!("Syntax error: extra arguments");
              }
            } else {
              panic!("Syntax error")
            }
          }
          "str.replacere" => {
            if let [var, old, new] = &arguments[..] {
              if let Term::QualIdentifier(qi) = var {
                Transduction(vec![TransductionOp::Replace(
                  get_var(qi, vars),
                  Regex::new(old),
                  ReplaceTarget::from(new, vars),
                )])
              } else {
                panic!("Syntax error: extra arguments");
              }
            } else {
              panic!("Syntax error")
            }
          }
          "str.reverse" => {
            if let [var] = &arguments[..] {
              if let Term::QualIdentifier(qi) = var {
                Transduction(vec![TransductionOp::Reverse(get_var(qi, vars))])
              } else {
                panic!("Syntax error: extra arguments");
              }
            } else {
              panic!("Syntax error")
            }
          }
          _ => panic!("Syntax error"),
        }
      }
      _ => panic!("Syntax error: {:?}", term),
    }
  }
}

type VarIndex = usize;

#[derive(Debug, PartialEq, Clone)]
pub struct StraightLineConstraint<T: FromChar, S: State>(
  pub(crate) VarIndex,
  pub(crate) Transduction<T, S>,
);
#[derive(Debug, PartialEq, Clone)]
pub struct RegularConstraint<T: FromChar>(pub(crate) VarIndex, pub(crate) Regex<T>);
#[derive(Debug, PartialEq, Clone)]
pub struct IntLinearConstraint(pub(crate) VarIndex, pub(crate) Vec<LinearTerm>);

#[derive(Debug, PartialEq, Clone)]
pub enum Constraint<T: FromChar, S: State> {
  STLine(StraightLineConstraint<T, S>),
  Reg(RegularConstraint<T>),
  #[allow(dead_code)]
  Linear(IntLinearConstraint),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Constraints<T: FromChar, S: State>(Vec<Constraint<T, S>>);
impl<T: FromChar, S: State> Constraints<T, S> {
  pub fn new(constraints: Vec<Constraint<T, S>>) -> Self {
    Constraints(constraints)
  }

  pub fn filter_sl(&self, idx: VarIndex) -> Option<&StraightLineConstraint<T, S>> {
    let mut filtered = self.0.iter().filter_map(|constraint| {
      if let Constraint::STLine(sl_cons) = constraint {
        if sl_cons.0 == idx {
          Some(sl_cons)
        } else {
          None
        }
      } else {
        None
      }
    });
    let constraint = filtered.next();
    if let None = filtered.next() {
      constraint
    } else {
      panic!("Given constraints are not straightline-constraint");
    }
  }

  pub fn filter_reg(&self, idx: VarIndex) -> Vec<&RegularConstraint<T>> {
    let filtered = self.0.iter().filter_map(|constraint| {
      if let Constraint::Reg(reg_cons) = constraint {
        if reg_cons.0 == idx {
          Some(reg_cons)
        } else {
          None
        }
      } else {
        None
      }
    });
    filtered.collect()
  }

  pub fn filter_int(&self, idx: VarIndex) -> Vec<&IntLinearConstraint> {
    let filtered = self.0.iter().filter_map(|constraint| {
      if let Constraint::Linear(il_cons) = constraint {
        if il_cons.0 == idx {
          Some(il_cons)
        } else {
          None
        }
      } else {
        None
      }
    });
    filtered.collect()
  }

  pub fn push(&mut self, constraint: Constraint<T, S>) {
    self.0.push(constraint);
  }

  pub fn iter(&self) -> std::slice::Iter<'_, Constraint<T, S>> {
    self.0.iter()
  }
}
impl<T: FromChar, S: State> FromIterator<Constraint<T, S>> for Constraints<T, S> {
  fn from_iter<It: IntoIterator<Item = Constraint<T, S>>>(iter: It) -> Self {
    let mut constraints = Constraints::new(vec![]);

    for constraint in iter {
      constraints.push(constraint)
    }

    constraints
  }
}
impl<T: FromChar, S: State> IntoIterator for Constraints<T, S> {
  type Item = Constraint<T, S>;
  type IntoIter = std::vec::IntoIter<Self::Item>;

  fn into_iter(self) -> Self::IntoIter {
    self.0.into_iter()
  }
}

#[derive(Debug, PartialEq)]
pub struct SMTOption {
  check_sat: bool,
  get_model: bool,
  logic: Logic,
}
impl Default for SMTOption {
  fn default() -> Self {
    SMTOption {
      check_sat: false,
      get_model: false,
      logic: Logic::QuantifierFreeString,
    }
  }
}

#[derive(PartialEq)]
pub enum Logic {
  QuantifierFreeString,
}
impl ToString for Logic {
  fn to_string(&self) -> String {
    match self {
      Logic::QuantifierFreeString => String::from("QF_STR"),
    }
  }
}
impl Debug for Logic {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.write_str(&self.to_string())
  }
}

#[derive(Debug, PartialEq)]
pub struct Smt2<T: FromChar, S: State> {
  constraints: Constraints<T, S>,
  vars: Variables,
  int_vars: Variables,
  option: SMTOption,
}
impl<T: FromChar, S: State> Smt2<T, S> {
  pub fn parse(input: &str) -> Result<Self, String> {
    let commands = CommandStream::new(input.as_bytes(), SyntaxBuilder, None)
      .collect::<Result<Vec<_>, _>>()
      .map_err(|err| err.to_string())?;
    let mut smt2 = Smt2::init();
    for command in commands.into_iter() {
      smt2.update(command);
    }
    Ok(smt2)
  }

  fn init() -> Self {
    Smt2 {
      constraints: Constraints::new(vec![]),
      vars: Vec::new(),
      int_vars: Vec::new(),
      option: SMTOption::default(),
    }
  }

  fn update(&mut self, command: Command) {
    match command {
      Command::DeclareConst {
        symbol: Symbol(var),
        sort,
      } => {
        if let Sort::Simple {
          identifier: Identifier::Simple { symbol: Symbol(s) },
        } = sort
        {
          match &s[..] {
            "String" | "string" => {
              if self.vars.iter().find(|&x| x == &var).is_none() {
                if self.int_vars.iter().find(|&x| x == &var).is_none() {
                  self.vars.push(var);
                } else {
                  panic!(
                    "Variable name confliction occured. Integer variable {} already defined.",
                    var
                  );
                }
              } else {
                panic!("String variable {} is already defined.", var);
              }
            }
            "Int" | "int" => {
              if self.int_vars.iter().find(|&x| x == &var).is_none() {
                if self.vars.iter().find(|&x| x == &var).is_none() {
                  self.int_vars.push(var);
                } else {
                  panic!(
                    "Variable name confliction occured. String variable {} already defined",
                    var
                  );
                }
              } else {
                panic!("Integer variable {} already defined", var);
              }
            }
            s => panic!("Unsupported type {}", s),
          }
        }
      }
      Command::Assert { term } => match term {
        Term::Application {
          qual_identifier,
          arguments,
        } => match get_symbol(&qual_identifier) {
          "=" => {
            if let [qi, transduction] = &arguments[..] {
              if let Term::QualIdentifier(qi) = qi {
                self
                  .constraints
                  .push(Constraint::STLine(StraightLineConstraint(
                    get_var(qi, &self.vars),
                    Transduction::from(transduction, &self.vars),
                  )))
              } else {
                unimplemented!()
              }
            } else {
              panic!("Syntax error")
            }
          }
          "str.in.re" => {
            if let [qi, reg] = &arguments[..] {
              if let Term::QualIdentifier(qi) = qi {
                self.constraints.push(Constraint::Reg(RegularConstraint(
                  get_var(qi, &self.vars),
                  Regex::new(reg),
                )))
              } else {
                panic!("Syntax error")
              }
            } else {
              panic!("Syntax error")
            }
          }
          s => eprintln!("Unsupported identifier: {}", s),
        },
        _ => eprintln!("Unsupported assertion: {:?}", term),
      },
      Command::CheckSat => self.option.check_sat = true,
      Command::GetModel => self.option.get_model = true,
      _ => eprintln!("Unsupported command: {:?}", command),
    }
  }

  pub fn straight_line(&self) -> Vec<StraightLineConstraint<T, S>> {
    let mut sl_cons = vec![];

    for idx in 0..self.vars.len() {
      if let Some(sl) = self.constraints.filter_sl(idx) {
        sl_cons.push(sl.clone());
      } else {
        sl_cons.push(StraightLineConstraint(idx, Transduction::empty()))
      }
    }

    sl_cons
  }

  pub fn regular(&self) -> Vec<RegularConstraint<T>> {
    self
      .constraints
      .iter()
      .filter_map(|constraint| {
        if let Constraint::Reg(reg) = constraint {
          Some(reg.clone())
        } else {
          None
        }
      })
      .collect()
  }

  pub fn int_linear(&self) -> Vec<IntLinearConstraint> {
    self
      .constraints
      .iter()
      .filter_map(|constraint| {
        if let Constraint::Linear(il) = constraint {
          Some(il.clone())
        } else {
          None
        }
      })
      .collect()
  }

  pub fn constraints(&self) -> &Constraints<T, S> {
    &self.constraints
  }

  pub fn vars(&self) -> &Variables {
    &self.vars
  }

  pub fn int_vars(&self) -> &Variables {
    &self.int_vars
  }

  pub fn check_sat(&self) -> bool {
    self.option.check_sat
  }

  pub fn get_model(&self) -> bool {
    self.option.get_model
  }

  pub fn logic(&self) -> &Logic {
    &self.option.logic
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::tests::helper::*;
  use std::rc::Rc;

  #[test]
  fn parse_correctly() {
    let input = r#"
    (declare-const x0 String)
    (declare-const x1 String)
    (declare-const x2 String)
    (declare-const i2 Int)
    (assert (= x1 (str.++ x0 x0)))
    (assert (= x2 (str.++ x1 x0 x1)))
    (assert (str.in.re x1 (re.+ (str.to.re "ab"))))
    (assert (str.in.re x2 (re.* (str.to.re "aa"))))
    (check-sat)
    "#;
    let smt2 = Smt2::<char, Rc<StateImpl>>::parse(input).unwrap();
    assert_eq!(
      &vec!["x0".to_string(), "x1".to_string(), "x2".to_string()],
      smt2.vars(),
    );
    assert_eq!(&vec!["i2".to_string()], smt2.int_vars(),);
    assert!(smt2.check_sat());
    assert!(!smt2.get_model());
    let mut sl_iter = smt2.straight_line().into_iter();
    assert_eq!(
      Some(StraightLineConstraint(0, Transduction(vec![]))),
      sl_iter.next()
    );
    assert_eq!(
      Some(StraightLineConstraint(
        1,
        Transduction(vec![TransductionOp::Var(0), TransductionOp::Var(0)])
      )),
      sl_iter.next()
    );
    assert_eq!(
      Some(StraightLineConstraint(
        2,
        Transduction(vec![
          TransductionOp::Var(1),
          TransductionOp::Var(0),
          TransductionOp::Var(1)
        ])
      )),
      sl_iter.next()
    );
    assert_eq!(None, sl_iter.next());
    let mut re_iter = smt2.regular().into_iter();
    let x1 = Regex::Element('a').concat(Regex::Element('b'));
    let x1 = x1.clone().concat(x1.star());
    assert_eq!(Some(RegularConstraint(1, x1)), re_iter.next());
    assert_eq!(
      Some(RegularConstraint(
        2,
        Regex::Element('a').concat(Regex::Element('a')).star()
      )),
      re_iter.next()
    );
    assert_eq!(None, re_iter.next());
    assert_eq!(None, smt2.int_linear().iter().next());
  }
}
