mod boolean_algebra;
pub mod regular;
pub mod smt2;
mod state;
pub mod transducer;
mod util;

use smt2::{Constraint, Smt2};
use state::{State, StateImpl, StateMachine};
use std::collections::HashMap;
use transducer::{sst_factory::SstBuilder, term::VariableImpl};
use util::{CharWrap, Domain};

#[derive(Debug, PartialEq)]
pub enum SolverResult {
  Sat,
  Model(HashMap<String, String>),
  Unsat,
}

pub fn check_sat<D: Domain, S: State>(mut smt2: Smt2<D, S>) -> SolverResult {
  let mut sfa = smt2.emit_sfa();

  let builder: SstBuilder<D, S, VariableImpl> = SstBuilder::init();

  for sl_cons in smt2.sl_constraints().into_iter().rev() {
    if sfa.final_set().is_empty() {
      break;
    }

    #[cfg(test)]
    {
      eprintln!("sl_cons: {:?}", sl_cons);
      eprintln!("sfa: {:?}", sfa);
    }
    let sst = builder.generate(sl_cons.idx(), sl_cons.constraint());
    #[cfg(test)]
    {
      //eprintln!("generated sst: {:?}", sst);
    }

    sfa = sfa.pre_image(sst);
  }

  #[cfg(test)]
  {
    eprintln!("sfa: {:#?}", sfa);
  }

  if smt2.get_model() {
    if let Some(path) = sfa.accepted_path() {
      #[cfg(test)]
      {
        eprintln!("accepted path {:?}", path);
      }
      SolverResult::Model(smt2.to_model(path))
    } else {
      SolverResult::Unsat
    }
  } else {
    if sfa
      .reachables(sfa.initial_state())
      .into_iter()
      .find(|s| sfa.final_set().contains(s))
      .is_some()
    {
      SolverResult::Sat
    } else {
      SolverResult::Unsat
    }
  }
}

pub fn parse(input: &str) -> Smt2<CharWrap, StateImpl> {
  let smt2 = Smt2::parse(input).unwrap();
  #[cfg(test)]
  {
    println!("{:?}", smt2);
  }
  smt2
}

pub fn run(input: &str) {
  let smt2 = parse(input);

  match check_sat(smt2) {
    SolverResult::Sat => println!("sat"),
    SolverResult::Unsat => println!("unsat"),
    SolverResult::Model(var_map) => {
      println!("sat");
      println!("given constraint is satisfiable with following assignment");
      for (var, assignment) in var_map {
        println!("{}:  {}", var, assignment);
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  pub(crate) mod helper {
    use super::*;
    pub use state::StateImpl;
    use transducer::term::OutputComp;
    pub use transducer::term::VariableImpl;
    use util::Domain;

    pub(crate) fn chars<T: Domain>(s: &str) -> Vec<T> {
      s.chars().map(|c| T::from(c)).collect()
    }

    pub(crate) fn to_replacer<T: Domain>(s: &str) -> Vec<OutputComp<T, VariableImpl>> {
      s.chars().map(|c| OutputComp::A(T::from(c))).collect()
    }

    pub(crate) fn to_charwrap<'a>(vs: impl IntoIterator<Item = &'a str>) -> Vec<CharWrap> {
      vs.into_iter()
        .map(|s| {
          let mut w: Vec<_> = s.chars().map(|c| CharWrap::from(c)).collect();
          w.push(CharWrap::separator());
          w
        })
        .reduce(|mut acc, v| {
          acc.extend(v);
          acc
        })
        .unwrap_or(vec![])
    }

    macro_rules! run {
      ($machine:expr, [$( $input:expr ),+]) => {{
        let mut input = vec![];
        $(
          input.extend($input.chars());
        )+
        $machine.run(&input)
      }};
      ($machine:expr, [$( $input:expr ),+], wrap) => {{
        use crate::util::CharWrap;
        let mut input = vec![];
        $(
          input.extend($input.chars().map(|c| CharWrap::from(c)));
          input.push(CharWrap::separator());
        )+
        $machine.run(&input)
      }};
    }

    pub(crate) use run;
  }

  macro_rules! model {
    ( $($var:expr => $result:expr),* $(,)? ) => {
      SolverResult::Model(HashMap::from([$(
        ($var.to_owned(), $result.to_owned())
      ),*]))
    };
  }

  #[test]
  fn smt2_2_sst_rev() {
    let input = r#"
      (declare-const x0 String)
      (declare-const x1 String)
      (assert (= x1 (str.reverse x0)))
      (assert (str.in.re x1 (str.to.re "ab")))
      (check-sat)
      (get-model)
      "#;

    assert_eq!(check_sat(parse(input)), model!["x0" => "ba","x1" => "ab"]);
  }

  #[test]
  fn smt2_2_sst_replace() {
    let input = r#"
      (declare-const x0 String)
      (declare-const x1 String)
      (assert (= x1 
        (str.replaceallre x0 (re.union (str.to.re "a") (str.to.re "k")) "x")
      ))
      (assert (str.in.re x1 (str.to.re "x")))
      (check-sat)
      (get-model)
      "#;

    let model = check_sat(parse(input));
    assert!(
      model == model!["x0" => "a", "x1" => "x"]
        || model == model!["x0" => "k", "x1" => "x"]
        || model == model!["x0" => "x", "x1" => "x"]
    );
  }

  #[test]
  fn smt2_2_sst_concat() {
    let input = r#"
      (declare-const x0 String)
      (declare-const x1 String)
      (assert (= x1 
        (str.++ "abc" x0 "www")
      ))
      (assert (str.in.re x1 (str.to.re "x")))
      (check-sat)
      (get-model)
      "#;

    assert_eq!(check_sat(parse(input)), SolverResult::Unsat);

    let input = r#"
      (declare-const x0 String)
      (declare-const x1 String)
      (assert (= x1 
        (str.++ "abc" x0 "w")
      ))
      (assert (str.in.re x1
        (
          re.++ (str.to.re "abc") re.allchar (re.+ (str.to.re "w"))
        )
      ))
      (check-sat)
      (get-model)
      "#;

    assert!({
      let mut result = false;
      let model = check_sat(parse(input));
      for i in 0..=5 {
        let x0 = format!("a{}", "w".repeat(i));
        if model == model!["x0" => x0, "x1" => format!("{}{}{}", "abc", x0, "w")] {
          result = true;
          break;
        }
      }
      result
    });
  }

  #[test]
  fn smt2_2_sst_variable() {
    let input = r#"
      (declare-const x0 String)
      (declare-const x1 String)
      (declare-const x2 String)
      (assert (= x1 x0))
      (assert (= x2 x1))
      (assert (str.in.re x1 (str.to.re "x")))
      (assert (str.in.re x2 (str.to.re "a")))
      (check-sat)
      (get-model)
      "#;

    assert_eq!(check_sat(parse(input)), SolverResult::Unsat);

    let input = r#"
      (declare-const x0 String)
      (declare-const x1 String)
      (declare-const x2 String)
      (assert (= x1 (str.reverse x0)))
      (assert (= x2 (str.++ x1 "a")))
      (assert (str.in.re x2 (str.to.re "aba")))
      (check-sat)
      (get-model)
      "#;

    assert_eq!(
      check_sat(parse(input)),
      model!["x0" => "ba", "x1" => "ab", "x2" => "aba"]
    );
  }

  #[test]
  fn smt2_2_sst_unsat() {
    let input = r#"
      (declare-const x0 String)
      (declare-const x1 String)
      (declare-const x2 String)
      (assert (= x1 (str.++ x0 (str.reverse x0))))
      (assert (= x2
        (str.++ x1
          (str.replaceallre x0
            (str.to.re "abc") "xyz"
          ) x1
        )
      ))
      (assert (str.in.re x1 (re.+ (str.to.re "ab"))))
      (assert (str.in.re x2 (re.* (str.to.re "xyz"))))
      (check-sat)
      (get-model)
      "#;

    assert_eq!(check_sat(parse(input)), SolverResult::Unsat);
  }

  #[test]
  #[ignore]
  fn smt2_2_sst_unstable() {
    let input = r#"
      (declare-const x0 String)
      (declare-const x1 String)
      (declare-const x2 String)
      (declare-const x3 String)
      (assert (= x1 (str.++ x0 x0)))
      (assert (= x2 (str.++ x1 x0 x1)))
      (assert (= x3 (str.replaceallre x2 (str.to.re "c") "x")))
      (assert (str.in.re x1 (re.+ (str.to.re "ab"))))
      (assert (str.in.re x2 (re.+ (str.to.re "ab"))))
      (check-sat)
      (get-model)
      "#;
    eprintln!("{:?}", check_sat(parse(input)));
    unreachable!();
  }
}
