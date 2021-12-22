pub mod sst;
pub mod sst_factory;
pub mod term;
pub mod transducer;

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    char_util::{CharWrap, FromChar},
    regular::regex::Regex,
    state::StateMachine,
    tests::helper::*,
  };
  use sst::Sst;
  use sst_factory::{self, SstBuilder};
  use std::iter::FromIterator;
  use std::rc::Rc;

  type TestSst<T> = Sst<T, StateImpl, VariableImpl>;

  struct Setup<'a, T = char>
  where
    T: FromChar,
  {
    regex: Regex<T>,
    replace_tar: &'a str,
  }
  impl<'a, T: FromChar> Setup<'a, T> {
    fn new() -> Self {
      let abc = Regex::seq("abc");
      let kkk = Regex::seq("kkk");
      let regex = abc.or(kkk);

      Self {
        regex,
        replace_tar: "xyz",
      }
    }

    fn replace(&self) -> TestSst<T> {
      SstBuilder::replace_reg(self.regex.clone(), to_replacer(self.replace_tar))
    }

    fn replace_all(&self) -> TestSst<T> {
      SstBuilder::replace_all_reg(self.regex.clone(), to_replacer(self.replace_tar))
    }

    fn id(&self) -> TestSst<T> {
      SstBuilder::identity()
    }

    fn reverse(&self) -> TestSst<T> {
      SstBuilder::reverse()
    }
  }

  //TODO -- ensure merge and chain work fine

  #[test]
  #[ignore]
  fn merge() {
    let setup: Setup<'_, char> = Setup::new();

    let rep_rev = setup.replace().merge(setup.reverse(), &VariableImpl::new());

    {
      assert_eq!(String::from_iter(&rep_rev.run(&chars(""))[0]), "");
      assert_eq!(String::from_iter(&rep_rev.run(&chars("abc"))[0]), "xyzcba");
      assert_eq!(String::from_iter(&rep_rev.run(&chars("kkk"))[0]), "xyzkkk");
      assert_eq!(
        String::from_iter(&rep_rev.run(&chars("ddabcee"))[0]),
        "ddxyzeeeecbadd"
      );
      assert_eq!(
        String::from_iter(&rep_rev.run(&chars("abcababcbcc"))[0]),
        "xyzababcbccccbcbabacba"
      );
    }

    let id_all = setup
      .id()
      .merge(setup.replace_all(), &Rc::new(VariableImpl::new()));

    {
      assert_eq!(String::from_iter(&id_all.run(&chars(""))[0]), "");
      assert_eq!(String::from_iter(&id_all.run(&chars("abc"))[0]), "abcxyz");
      assert_eq!(String::from_iter(&id_all.run(&chars("kkk"))[0]), "kkkxyz");
      assert_eq!(
        String::from_iter(&id_all.run(&chars("ddabcee"))[0]),
        "ddabceeddxyzee"
      );
      assert_eq!(
        String::from_iter(&id_all.run(&chars("abcababcbcc"))[0]),
        "abcababcbccxyzabxyzbcc"
      );
    }
  }

  #[test]
  #[ignore]
  fn duplicating_correctly() {
    let setup: Setup<'_, char> = Setup::new();

    let id = setup.id();
    assert!(id.states().len() == 1 && id.variables().len() == 1);
    assert_eq!(String::from_iter(&id.run(&chars("xyz"))[0]), "xyz");
    let dup = id.merge(setup.id(), &VariableImpl::new());
    assert!(dup.states().len() == 1 && dup.variables().len() == 2);
    assert_eq!(String::from_iter(&dup.run(&chars("xyz"))[0]), "xyzxyz");
    let tri = dup.merge(setup.id(), &VariableImpl::new());
    assert!(tri.states().len() == 1 && tri.variables().len() == 3);
    assert_eq!(String::from_iter(&tri.run(&chars("xyz"))[0]), "xyzxyzxyz");
    let qua = tri.merge(setup.id(), &VariableImpl::new());
    assert!(qua.states().len() == 1 && qua.variables().len() == 4);
    assert_eq!(
      String::from_iter(&qua.run(&chars("xyz"))[0]),
      "xyzxyzxyzxyz"
    );
  }

  #[test]
  #[ignore]
  fn chain() {
    let setup: Setup<'_, CharWrap> = Setup::new();

    let first = setup.id().merge(setup.replace(), &VariableImpl::new());
    assert_eq!(
      first.run(&to_charwrap(&["abcabc"])).last(),
      Some(&to_charwrap(&["abcabcxyzabc"]))
    );
    let second = first.chain(setup.reverse());
    assert_eq!(
      second.run(&to_charwrap(&["abcabc", "edf"])).last(),
      Some(&to_charwrap(&["abcabcxyzabc", "fde"]))
    );
    let third = second.chain(setup.replace_all());

    {
      assert_eq!(third.run(&to_charwrap(&[])), Vec::<Vec<_>>::new());
      eprintln!(
        "{:#?}",
        third.run(&to_charwrap(&["abcabc", "abcabc", "abcabc"]))
      );
      assert_eq!(
        third.run(&to_charwrap(&["abcabc", "abcabc", "abcabc"])),
        vec![to_charwrap(&["abcabcxyzabc", "cbacba", "xyzxyz"])]
      );
    }
  }
}
