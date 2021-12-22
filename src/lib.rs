mod boolean_algebra;
mod char_util;
pub mod regular;
pub mod smt2;
mod state;
pub mod transducer;

use char_util::CharWrap;
use smt2::Smt2;
use state::StateImpl;
use std::{env, fs::File, io::Read, rc::Rc};

pub fn run() {
  let mut args = env::args();
  args.next();
  let mut input = String::new();
  for arg in args {
    if arg.starts_with("--") {
    } else if arg.starts_with("-") {
    } else {
      File::open(arg).unwrap().read_to_string(&mut input).unwrap();
    }
  }

  let smt2 = Smt2::<CharWrap, Rc<StateImpl>>::parse(&input).unwrap();

  println!("{:?}", smt2);
}

#[cfg(test)]
mod tests {
  use super::*;
  use regular::{recognizable::Recognizable, regex::Regex};
  use transducer::sst_factory::SstBuilder;

  type Builder = SstBuilder<CharWrap, StateImpl, VariableImpl>;
  type Smt = Smt2<CharWrap, StateImpl>;

  pub mod helper {
    use super::*;
    use char_util::FromChar;
    pub use state::StateImpl;
    use transducer::term::OutputComp;
    pub use transducer::term::VariableImpl;

    pub fn chars<T: FromChar>(s: &str) -> Vec<T> {
      s.chars().map(|c| T::from_char(c)).collect()
    }

    pub fn to_replacer<T: FromChar>(s: &str) -> Vec<OutputComp<T, VariableImpl>> {
      s.chars().map(|c| OutputComp::A(T::from_char(c))).collect()
    }

    pub fn to_charwrap<T: FromChar>(vs: &[&str]) -> Vec<T> {
      vs.into_iter()
        .map(|s| {
          let mut w = s.chars().map(|c| T::from_char(c)).collect::<Vec<_>>();
          w.push(T::separator());
          w
        })
        .reduce(|mut acc, v| {
          acc.extend(v);
          acc
        })
        .unwrap_or(vec![])
    }
  }

  use helper::*;

  #[test]
  fn symbolic_pre_image() {
    let abc_to_xyz = Builder::replace_all_reg(Regex::seq("abc"), to_replacer("xyz"));
    let xyz_ = Regex::seq("xyz")
      .concat(Regex::All.star())
      .to_sym_fa::<StateImpl>();

    {
      assert!(xyz_.member(&chars("xyz")));
      assert!(xyz_.member(&chars("xyzfff")));
      assert!(!xyz_.member(&chars("xy")));
      assert!(!xyz_.member(&chars("abc")));
      assert!(!xyz_.member(&chars("abcfff")));
      assert!(!xyz_.member(&chars("ab")));
      assert!(!xyz_.member(&chars("kkk")));
    }

    let abc_ = xyz_.pre_image(abc_to_xyz);

    eprintln!("pre states: {:?}", abc_.states);
    eprintln!("pre trans: {:?}", abc_.transition);
    eprintln!("pre init: {:?}", abc_.initial_state);
    eprintln!("pre fs: {:?}", abc_.final_states);

    {
      assert!(abc_.member(&chars("xyz")));
      assert!(abc_.member(&chars("xyzfff")));
      assert!(!abc_.member(&chars("xy")));
      assert!(abc_.member(&chars("abc")));
      assert!(abc_.member(&chars("abcfff")));
      assert!(!abc_.member(&chars("ab")));
      assert!(!abc_.member(&chars("kkk")));
    }
  }

  #[test]
  fn smt2_2_sst() {
    let input = r#"
      (declare-const x0 String)
      (declare-const x1 String)
      (declare-const x2 String)
      (declare-const x3 String)
      (declare-const i2 Int)
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

    let smt2 = Smt::parse(input).unwrap();

    let sst_builder = Builder::init(smt2.vars().len());

    let ssts = sst_builder.generate(smt2.straight_line());

    if let [sst0, sst1, sst2, sst3, ..] = &ssts[..] {
      eprintln!("sst0 output:\n{:?}", sst0.run(&to_charwrap(&vec!["abc"])));

      eprintln!(
        "sst1 output:\n{:?}",
        sst1.run(&to_charwrap(&vec!["abcdefg"]))
      );

      eprintln!(
        "sst2 output:\n{:?}",
        sst2.run(&to_charwrap(&vec!["kkkoooabcababc", "cdf"]))
      );

      eprintln!(
        "sst3 output:\n{:?}",
        sst3.run(&to_charwrap(&vec!["1", "2", "3"]))
      );
    } else {
      unreachable!()
    }

    unimplemented!()
  }
}
