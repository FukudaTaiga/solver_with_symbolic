use super::regular::regex::Regex;
use super::transducer::transducer::Transducer;
use smt2parser::{
  concrete::{Command, Constant, Identifier, QualIdentifier, Sort, Symbol, SyntaxBuilder, Term},
  CommandStream, Numeral,
};
use std::fs::{self};

type Variables = Vec<String>;

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

fn get_var_from_str<'a>(target: &'a str, vars: &Variables) -> usize {
  if let Some(idx) = vars.iter().position(|s| s == target) {
    idx
  } else {
    panic!("Variable not found")
  }
}

fn get_var<'a>(qi: &QualIdentifier, vars: &Variables) -> usize {
  get_var_from_str(&get_symbol(qi), vars)
}

#[derive(Debug, PartialEq)]
struct LinearTerm {
  var: Option<usize>,
  coefficient: Numeral,
}

#[derive(Debug, PartialEq)]
enum ReplaceTarget {
  Str(String),
  Var(usize),
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

#[derive(Debug, PartialEq)]
enum TrOp {
  Reverse(usize),
  Str(String),
  Replace(usize, Regex<char>, ReplaceTarget),
  ReplaceAll(usize, Regex<char>, ReplaceTarget),
  UserDef(Transducer<char>),
}

#[derive(Debug, PartialEq)]
struct Transduction(Vec<TrOp>);
impl Transduction {
  pub fn from(term: &Term, vars: &Variables) -> Self {
    match term {
      Term::Constant(Constant::String(s)) => Transduction(vec![TrOp::Str(s.clone())]),
      Term::Application {
        qual_identifier,
        arguments,
      } => {
        let op = get_symbol(qual_identifier);
        match &op[..] {
          "str.++" => {
            if let [left, right] = &arguments[..] {
              let mut left = Transduction::from(left, vars);
              let mut right = Transduction::from(right, vars);
              left.0.append(&mut right.0);
              left
            } else {
              panic!("Syntax error")
            }
          }
          "str.replaceallre" => {
            if let [var, old, new] = &arguments[..] {
              if let Term::QualIdentifier(qi) = var {
                Transduction(vec![TrOp::ReplaceAll(
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
                Transduction(vec![TrOp::Replace(
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
                Transduction(vec![TrOp::Reverse(get_var(qi, vars))])
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
      _ => panic!("Invalid right hand side"),
    }
  }
}

#[derive(Debug, PartialEq)]
enum Constraint {
  STLine(usize, Transduction),
  Reg(usize, Regex<char>),
  Linear(usize, Vec<LinearTerm>),
}

fn to_constraint(
  command: Command,
  vars: &mut Variables,
  int_vars: &mut Variables,
  constraints: &mut Vec<Constraint>,
) {
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
          "String" | "string" => vars.push(var),
          "Int" | "int" => int_vars.push(var),
          _ => panic!("Syntax error"),
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
              constraints.push(Constraint::STLine(
                get_var(qi, vars),
                Transduction::from(transduction, vars),
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
              constraints.push(Constraint::Reg(get_var(qi, vars), Regex::new(reg)))
            } else {
              panic!("Syntax error")
            }
          } else {
            panic!("Syntax error")
          }
        }
        _ => unimplemented!(),
      },
      _ => unimplemented!(),
    },
    Command::CheckSat => eprintln!("check sat!"),
    _ => eprintln!("Invalid command {:?}", command),
  }
}

pub fn parse_smt2(filename: String) -> Result<(), &'static str> {
  let input = fs::read_to_string(filename).unwrap();
  let commands = CommandStream::new(input.as_bytes(), SyntaxBuilder, None)
    .collect::<Result<Vec<_>, _>>()
    .unwrap();
  let mut constraints = vec![];
  let mut vars = vec![];
  let mut int_vars = vec![];
  
  for command in commands.into_iter() {
    to_constraint(command, &mut vars, &mut int_vars, &mut constraints)
  }

  for (i, constraint) in constraints.iter().enumerate() {
    eprintln!("{} constraint", i);
    eprintln!("{:#?}", constraint);
  }

  for (i, var) in vars.iter().enumerate() {
    eprintln!("{} - {}", var, i)
  }

  for (i, var) in int_vars.iter().enumerate() {
    eprintln!("{} - {}", var, i)
  }

  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn aaaa() {
    parse_smt2("test.smt2".to_string()).unwrap();
    unimplemented!();
  }
}
