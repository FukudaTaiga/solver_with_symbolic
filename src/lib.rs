mod boolean_algebra;
pub mod regular;
pub mod smt2;
mod state;
pub mod transducer;
mod util;

use boolean_algebra::Predicate;
use smt2::{Constraint, Smt2};
use state::{StateImpl, StateMachine};
use transducer::{sst_factory::SstBuilder, term::VariableImpl};
use util::{CharWrap, Domain};

#[derive(Debug, PartialEq)]
pub enum SolverResult {
  SAT,
  Model(std::collections::HashMap<String, String>),
  UNSAT,
}

pub fn run(input: &str) -> SolverResult {
  let mut smt2 = Smt2::<CharWrap, StateImpl>::parse(input).unwrap();
  println!("{:?}", smt2);

  let mut sfa = smt2.emit_sfa();

  let builder: SstBuilder<CharWrap, StateImpl, VariableImpl> = SstBuilder::init();

  while let Some(sl_cons) = smt2.next() {
    eprintln!("sfa: {:?}", sfa);
    eprintln!("sl_cons: {:?}", sl_cons);
    let sst = builder.generate(sl_cons.idx(), sl_cons.constraint());
    eprintln!("generated sst: {:?}", sst);

    sfa = sfa.pre_image(sst);
  }

  eprintln!("sfa: {:#?}", sfa);

  if smt2.get_model() {
    if let Some(path) = sfa.accepted_path() {
      SolverResult::Model(smt2.to_model(path))
    } else {
      SolverResult::UNSAT
    }
  } else {
    if sfa
      .reachables(sfa.initial_state())
      .into_iter()
      .find(|s| sfa.final_set().contains(s))
      .is_some()
    {
      SolverResult::SAT
    } else {
      SolverResult::UNSAT
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

  #[test]
  #[ignore]
  fn smt2_2_sst_simple() {
    let input = r#"
      (declare-const x0 String)
      (declare-const x1 String)
      (assert (= x1 (str.reverse x0)))
      (assert (str.in.re x1 (re.* (str.to.re "ab"))))
      (check-sat)
      (get-model)
      "#;

    assert_eq!(run(input), SolverResult::SAT);

    unimplemented!()
  }

  #[test]
  #[ignore]
  fn smt2_2_sst_complex() {
    let input = r#"
      (declare-const x0 String)
      (declare-const x1 String)
      (declare-const x2 String)
      (assert (= x1 (str.++ x0 (str.reverse x0))))
      (assert (= x2
        (str.++ x1
          (str.replaceallre x0
            (re.union (str.to.re "abc") (str.to.re "kkk")) "xyz"
          ) x1
        )
      ))
      (assert (str.in.re x1 (re.+ (str.to.re "ab"))))
      (assert (str.in.re x2 (re.* (str.to.re "aa"))))
      (check-sat)
      "#;

    assert_eq!(run(input), SolverResult::SAT);

    unimplemented!()
  }
}
