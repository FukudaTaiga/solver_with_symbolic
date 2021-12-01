pub mod sst;
pub mod sst_factory;
pub mod term;
pub mod transducer;

#[cfg(test)]
mod tests {
  use super::term::OutputComp;
  use super::*;
  use crate::char_util::{CharWrap, FromChar};
  use crate::regular::regex::Regex;
  use crate::state::{State, StateMachine};
  use sst::Sst;
  use sst_factory::SstBuilder;
  use std::iter::FromIterator;
  use std::rc::Rc;
  use term::Variable;

  fn chars(s: &str) -> Vec<char> {
    s.chars().collect::<Vec<char>>()
  }

  fn to_charwrap(vs: &[&str]) -> Vec<CharWrap> {
    vs.into_iter()
      .map(|s| {
        s.chars()
          .map(|c| CharWrap::from_char(c))
          .collect::<Vec<_>>()
      })
      .reduce(|mut acc: Vec<CharWrap>, v| {
        acc.push(CharWrap::Separator);
        acc.extend(v);
        acc
      })
      .unwrap_or(vec![])
  }

  struct Setup<'a> {
    regex: Regex<char>,
    regex_wrap: Regex<CharWrap>,
    replace_tar: &'a str,
  }
  impl<'a> Setup<'a> {
    fn new() -> Self {
      let abc = Regex::Element('a')
        .concat(Regex::Element('b'))
        .concat(Regex::Element('c'));
      let kkk = Regex::Element('k')
        .concat(Regex::Element('k'))
        .concat(Regex::Element('k'));
      let regex = abc.or(kkk);
      let abc = Regex::Element(CharWrap::Char('a'))
        .concat(Regex::Element(CharWrap::Char('b')))
        .concat(Regex::Element(CharWrap::Char('c')));
      let kkk = Regex::Element(CharWrap::Char('k'))
        .concat(Regex::Element(CharWrap::Char('k')))
        .concat(Regex::Element(CharWrap::Char('k')));
      let regex_wrap = abc.or(kkk);

      Self {
        regex,
        regex_wrap,
        replace_tar: "xyz",
      }
    }

    fn replace(&self) -> Sst<char, Rc<State>, Rc<Variable>> {
      let builder = SstBuilder::blank();
      builder.replace_reg(
        self.regex.clone(),
        self.replace_tar.chars().map(|c| OutputComp::A(c)).collect(),
      )
    }

    fn replace_all(&self) -> Sst<char, Rc<State>, Rc<Variable>> {
      let builder = SstBuilder::blank();
      builder.replace_all_reg(
        self.regex.clone(),
        self.replace_tar.chars().map(|c| OutputComp::A(c)).collect(),
      )
    }

    fn id(&self) -> Sst<char, Rc<State>, Rc<Variable>> {
      let builder = SstBuilder::blank();
      builder.identity()
    }

    fn reverse(&self) -> Sst<char, Rc<State>, Rc<Variable>> {
      let builder = SstBuilder::blank();
      builder.reverse()
    }

    fn replace_wrap(&self) -> Sst<CharWrap, Rc<State>, Rc<Variable>> {
      let builder = SstBuilder::blank();
      builder.replace_reg(
        self.regex_wrap.clone(),
        self
          .replace_tar
          .chars()
          .map(|c| OutputComp::A(CharWrap::from_char(c)))
          .collect(),
      )
    }

    fn replace_all_wrap(&self) -> Sst<CharWrap, Rc<State>, Rc<Variable>> {
      let builder = SstBuilder::blank();
      builder.replace_all_reg(
        self.regex_wrap.clone(),
        self
          .replace_tar
          .chars()
          .map(|c| OutputComp::A(CharWrap::from_char(c)))
          .collect(),
      )
    }

    fn id_wrap(&self) -> Sst<CharWrap, Rc<State>, Rc<Variable>> {
      let builder = SstBuilder::blank();
      builder.identity()
    }

    fn reverse_wrap(&self) -> Sst<CharWrap, Rc<State>, Rc<Variable>> {
      let builder = SstBuilder::blank();
      builder.reverse()
    }
  }

  #[test]
  fn update_merge() {
    let setup = Setup::new();

    let rep_rev = setup.replace().update_merge(setup.reverse());

    {
      assert_eq!(String::from_iter(&rep_rev.run(&chars("")[..])[0]), "");
      assert_eq!(
        String::from_iter(&rep_rev.run(&chars("abc")[..])[0]),
        "xyzcba"
      );
      assert_eq!(
        String::from_iter(&rep_rev.run(&chars("kkk")[..])[0]),
        "xyzkkk"
      );
      assert_eq!(
        String::from_iter(&rep_rev.run(&chars("ddabcee")[..])[0]),
        "ddxyzeeeecbadd"
      );
      assert_eq!(
        String::from_iter(&rep_rev.run(&chars("abcababcbcc")[..])[0]),
        "xyzababcbccccbcbabacba"
      );
    }

    let id_all = setup.id().update_merge(setup.replace_all());

    {
      assert_eq!(String::from_iter(&id_all.run(&chars("")[..])[0]), "");
      assert_eq!(
        String::from_iter(&id_all.run(&chars("abc")[..])[0]),
        "abcxyz"
      );
      assert_eq!(
        String::from_iter(&id_all.run(&chars("kkk")[..])[0]),
        "kkkxyz"
      );
      assert_eq!(
        String::from_iter(&id_all.run(&chars("ddabcee")[..])[0]),
        "ddabceeddxyzee"
      );
      assert_eq!(
        String::from_iter(&id_all.run(&chars("abcababcbcc")[..])[0]),
        "abcababcbccxyzabxyzbcc"
      );
    }
  }

  #[test]
  fn duplicating_correctly() {
    let setup = Setup::new();

    let id = setup.id();
    assert!(id.states().len() == 1 && id.variables().len() == 1);
    assert_eq!(String::from_iter(&id.run(&chars("xyz")[..])[0]), "xyz");
    let dup = id.update_merge(setup.id());
    assert!(dup.states().len() == 1 && dup.variables().len() == 2);
    assert_eq!(String::from_iter(&dup.run(&chars("xyz")[..])[0]), "xyzxyz");
    let tri = dup.update_merge(setup.id());
    assert!(tri.states().len() == 1 && tri.variables().len() == 3);
    assert_eq!(
      String::from_iter(&tri.run(&chars("xyz")[..])[0]),
      "xyzxyzxyz"
    );
    let qua = tri.update_merge(setup.id());
    assert!(qua.states().len() == 1 && qua.variables().len() == 4);
    assert_eq!(
      String::from_iter(&qua.run(&chars("xyz")[..])[0]),
      "xyzxyzxyzxyz"
    );
  }

  #[test]
  fn chain() {
    let setup = Setup::new();

    let first = setup.id_wrap().update_merge(setup.replace_wrap());
    eprintln!("{:#?}", first.run(&to_charwrap(&["abcabc"])[..]));
    assert_eq!(
      first.run(&to_charwrap(&["abcabc"])[..]).last(),
      Some(&to_charwrap(&["abcabcxyzabc"]))
    );
    let second = first.chain(setup.reverse_wrap());
    assert_eq!(
      second.run(&to_charwrap(&["abcabc", "edf"])[..]).last(),
      Some(&to_charwrap(&["abcabcxyzabc", "fde"]))
    );
    let third = second.chain(setup.replace_all_wrap());

    {
      assert_eq!(third.run(&to_charwrap(&[])[..]), Vec::<Vec<_>>::new());
      eprintln!(
        "{:#?}",
        third.run(&to_charwrap(&["abcabc", "abcabc", "abcabc"])[..])
      );
      assert_eq!(
        third.run(&to_charwrap(&["abcabc", "abcabc", "abcabc"])[..]),
        vec![to_charwrap(&["abcabcxyzabc", "cbacba", "xyzxyz"])]
      );
    }
  }
}
