use crate::boolean_algebra::BoolAlg;
use crate::regular::{
  regex::{self, Regex},
  symbolic_automata::Sfa,
};
use crate::state::State;
use crate::transducer::sst_factory::SstBuilder;
use crate::transducer::{
  term::{OutputComp, VariableImpl},
  transducer::Transducer,
};
use crate::util::Domain;
use smt2parser::{
  concrete::{Command, Constant, Identifier, QualIdentifier, Sort, Symbol, SyntaxBuilder, Term},
  CommandStream, Error as Smt2ParserError, Numeral,
};
use std::{collections::HashMap, fmt::Debug};

type VarIndex = usize;
pub type Variables = Vec<String>;

pub fn get_symbol(qi: &QualIdentifier) -> &str {
  if let QualIdentifier::Simple {
    identifier: Identifier::Simple {
      symbol: Symbol(symbol),
    },
  } = qi
  {
    symbol
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
pub enum TransductionOp<T: Domain, S: State> {
  Var(VarIndex),
  Reverse(VarIndex),
  Str(String),
  Replace(VarIndex, Regex<T>, ReplaceTarget),
  ReplaceAll(VarIndex, Regex<T>, ReplaceTarget),
  #[allow(dead_code)]
  UserDef(Transducer<T, S>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Transduction<D: Domain, S: State>(pub Vec<TransductionOp<D, S>>);
impl<D: Domain, S: State> Transduction<D, S> {
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

  pub fn apply(&self, var_map: &HashMap<VarIndex, String>) -> String {
    let mut result = String::new();

    for operator in &self.0 {
      match operator {
        TransductionOp::Str(s) => {
          result.push_str(&s);
        }
        TransductionOp::Var(idx) => {
          result.push_str(var_map.get(&idx).unwrap());
        }
        TransductionOp::Reverse(idx) => {
          result.push_str(&var_map.get(&idx).unwrap().chars().rev().collect::<String>());
        }
        TransductionOp::Replace(idx, from, to) => {
          let to = match to {
            ReplaceTarget::Str(s) => s.chars().map(|c| OutputComp::A(char::from(c))).collect(),
            ReplaceTarget::Var(target_id) => var_map
              .get(&target_id)
              .unwrap()
              .chars()
              .map(|c| OutputComp::A(char::from(c)))
              .collect(),
          };
          let sst =
            SstBuilder::<char, S, VariableImpl>::replace_reg(regex::convert(from.clone()), to);
          let chars: Vec<_> = var_map.get(&idx).unwrap().chars().collect();
          let replaced = sst.run(&chars[..]).get(0).unwrap()[..]
            .into_iter()
            .collect::<String>();
          result.push_str(&replaced);
        }
        TransductionOp::ReplaceAll(idx, from, to) => {
          let to = match to {
            ReplaceTarget::Str(s) => s.chars().map(|c| OutputComp::A(char::from(c))).collect(),
            ReplaceTarget::Var(target_id) => var_map
              .get(&target_id)
              .unwrap()
              .chars()
              .map(|c| OutputComp::A(char::from(c)))
              .collect(),
          };
          let sst =
            SstBuilder::<char, S, VariableImpl>::replace_all_reg(regex::convert(from.clone()), to);
          let chars: Vec<_> = var_map.get(&idx).unwrap().chars().collect();
          let replaced = sst.run(&chars[..]).get(0).unwrap()[..]
            .into_iter()
            .collect::<String>();
          result.push_str(&replaced);
        }
        TransductionOp::UserDef(_) => unimplemented!(),
      }
    }

    result
  }
}

pub trait Constraint {
  type Value;

  fn idx(&self) -> VarIndex;
  fn constraint(&self) -> &Self::Value;
}
#[derive(Debug, PartialEq, Clone)]
pub struct StraightLineConstraint<D: Domain, S: State>(VarIndex, Transduction<D, S>);
impl<D: Domain, S: State> Constraint for StraightLineConstraint<D, S> {
  type Value = Transduction<D, S>;

  fn idx(&self) -> VarIndex {
    self.0
  }
  fn constraint(&self) -> &Self::Value {
    &self.1
  }
}
#[derive(Debug, PartialEq, Clone)]
pub struct RegularConstraint<D: Domain>(VarIndex, Regex<D>);
impl<D: Domain> Constraint for RegularConstraint<D> {
  type Value = Regex<D>;

  fn idx(&self) -> VarIndex {
    self.0
  }
  fn constraint(&self) -> &Self::Value {
    &self.1
  }
}
#[derive(Debug, PartialEq, Clone)]
pub struct IntLinearConstraint(VarIndex, Vec<LinearTerm>);
impl Constraint for IntLinearConstraint {
  type Value = Vec<LinearTerm>;

  fn idx(&self) -> VarIndex {
    self.0
  }
  fn constraint(&self) -> &Self::Value {
    &self.1
  }
}

#[derive(Debug, PartialEq, Clone)]
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

#[derive(PartialEq, Clone)]
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
pub enum SolverResult<B: BoolAlg> {
  SAT,
  Model(Vec<B>),
  UNSAT,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Smt2<D: Domain, S: State> {
  sl_constraints: Vec<StraightLineConstraint<D, S>>,
  reg_constraints: Vec<RegularConstraint<D>>,
  vars: Variables,
  int_vars: Variables,
  option: SMTOption,
}
impl<D: Domain, S: State> Smt2<D, S> {
  pub fn parse(input: &str) -> Result<Self, Smt2ParserError> {
    let commands = CommandStream::new(input.as_bytes(), SyntaxBuilder, None)
      .collect::<Result<Vec<_>, _>>()
      .map_err(|err| err)?;
    let mut smt2 = Smt2::init();
    for command in commands.into_iter() {
      smt2.update(command);
    }
    Ok(smt2)
  }

  fn init() -> Self {
    Smt2 {
      sl_constraints: vec![],
      reg_constraints: vec![],
      vars: vec![],
      int_vars: vec![],
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
                self.sl_constraints.push(StraightLineConstraint(
                  get_var(qi, &self.vars),
                  Transduction::from(transduction, &self.vars),
                ))
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
                self
                  .reg_constraints
                  .push(RegularConstraint(get_var(qi, &self.vars), Regex::new(reg)))
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

  pub fn emit_sfa(&mut self) -> Sfa<D, S> {
    assert_ne!(self.vars.len(), 0);
    (0..self.vars.len())
      .into_iter()
      .map(|idx| {
        self
          .filter_reg(idx)
          .map(|reg| reg.to_sfa())
          .unwrap_or_default()
      })
      .reduce(|result, sfa| result.chain(sfa))
      .map(|sfa| sfa.finish())
      .expect("no string constraint given")
  }

  pub fn filter_sl(&self, idx: VarIndex) -> Option<&StraightLineConstraint<D, S>> {
    self
      .sl_constraints
      .iter()
      .find(|sl_cons| sl_cons.idx() == idx)
  }

  pub fn filter_reg(&mut self, idx: VarIndex) -> Option<Regex<D>> {
    let mut result: Option<Regex<D>> = None;

    while let Some(i) = self
      .reg_constraints
      .iter()
      .position(|reg_cons| reg_cons.idx() == idx)
    {
      let regex = self.reg_constraints.swap_remove(i).1;
      result = Some(match result {
        Some(result) => result.inter(regex),
        None => regex,
      });
    }

    result
  }

  pub fn sl_constraints(&self) -> &Vec<StraightLineConstraint<D, S>> {
    &self.sl_constraints
  }

  pub fn reg_constraints(&self) -> &Vec<RegularConstraint<D>> {
    &self.reg_constraints
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

  pub fn to_model<B: BoolAlg>(&self, path: Vec<B>) -> HashMap<String, String> {
    let mut result = HashMap::new();
    let mut idx = 0usize;

    path.into_iter().for_each(|predicate| {
      assert!(idx < self.vars.len());
      let s = result.entry(idx).or_insert(String::new());

      if predicate == B::char(B::Domain::separator()) {
        idx += 1;
      } else {
        s.push(predicate.get_one().unwrap().into());
      }
    });

    while idx < self.vars.len() {
      result.insert(idx, self.filter_sl(idx).unwrap().1.apply(&result));
      idx += 1;
    }

    result
      .into_iter()
      .map(|(idx, s)| (self.vars[idx].clone(), s.clone()))
      .collect()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::tests::helper::*;

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
    let smt2 = Smt2::<char, StateImpl>::parse(input).unwrap();
    assert_eq!(
      &vec!["x0".to_string(), "x1".to_string(), "x2".to_string()],
      smt2.vars(),
    );
    assert_eq!(&vec!["i2".to_string()], smt2.int_vars(),);
    assert!(smt2.check_sat());
    assert!(!smt2.get_model());
    let mut sl_iter = smt2.sl_constraints().clone().into_iter();
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
    let mut re_iter = smt2.reg_constraints().clone().into_iter();
    assert_eq!(
      Some(RegularConstraint(
        1,
        Regex::Element('a').concat(Regex::Element('b')).plus()
      )),
      re_iter.next()
    );
    assert_eq!(
      Some(RegularConstraint(
        2,
        Regex::Element('a').concat(Regex::Element('a')).star()
      )),
      re_iter.next()
    );
    assert_eq!(None, re_iter.next());
  }
}
