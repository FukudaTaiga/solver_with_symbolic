pub mod recognizable;
pub mod regex;
pub mod symbolic_automata;

#[cfg(test)]
mod tests {
  use super::recognizable::Recognizable;
  use super::regex::Regex;
  use crate::state::State;
  use std::rc::Rc;

  #[test]
  fn reg_sfa_all() {
    let reg = Regex::parse("_").unwrap();
    let reg2 = Regex::parse("_*").unwrap();
    let sfa = reg.to_sym_fa::<Rc<State>>();
    let sfa2 = reg2.to_sym_fa::<Rc<State>>();

    {
      assert!(sfa.member(&"a".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.member(&"x".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.member(&"$".chars().collect::<Vec<char>>()[..]));
      assert!(sfa2.member(&"cdsnjcdskcnsdjk".chars().collect::<Vec<char>>()[..]));
      assert!(sfa2.member(&"xxxxxxx".chars().collect::<Vec<char>>()[..]));
      assert!(sfa2.member(&":cdskoapcd".chars().collect::<Vec<char>>()[..]));
      assert!(sfa2.member(&"".chars().collect::<Vec<char>>()[..]));
    }

    {
      assert!(!sfa.member(&"".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"ax".chars().collect::<Vec<char>>()[..]));
    }
  }

  #[test]
  fn reg_sfa_epsilon() {
    let reg = Regex::parse("!*").unwrap();
    let reg2 = Regex::parse("avc(!*)").unwrap();
    let sfa = reg.to_sym_fa::<Rc<State>>();
    let sfa2 = reg2.to_sym_fa::<Rc<State>>();

    {
      assert!(sfa.member(&"".chars().collect::<Vec<char>>()[..]));
      assert!(sfa2.member(&"avc".chars().collect::<Vec<char>>()[..]));
    }

    {
      assert!(!sfa.member(&"ab".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa2.member(&"av".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"xxxxx".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"avcs".chars().collect::<Vec<char>>()[..]));
    }
  }

  #[test]
  fn reg_sfa_star() {
    let reg = Regex::parse("w(a*)x(b*)y(c*)z").unwrap();
    let sfa = reg.to_sym_fa::<Rc<State>>();

    {
      assert!(sfa.member(&"waaaxbyccccz".chars().collect::<Vec<char>>()[..]));

      assert!(sfa.member(&"waaaxyccccz".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.member(&"wxbyccccz".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.member(&"waaaxbyz".chars().collect::<Vec<char>>()[..]));

      assert!(sfa.member(&"waaaxyz".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.member(&"wxbyz".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.member(&"wxyccccz".chars().collect::<Vec<char>>()[..]));

      assert!(sfa.member(&"wxyz".chars().collect::<Vec<char>>()[..]));
    }

    {
      assert!(!sfa.member(&"aabbcc".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"waxbyc".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"axbycz".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"waxbcz".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"wabycz".chars().collect::<Vec<char>>()[..]));
    }
  }

  #[test]
  fn reg_sfa_concat() {
    let reg = Regex::parse("(_*)abc(abc*)(_*)").unwrap();
    let sfa = reg.to_sym_fa::<Rc<State>>();

    {
      assert!(sfa.member(&"xxzxabcde".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.member(&"abc".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.member(&"xxxzabcabcabcxe".chars().collect::<Vec<char>>()[..]));
    }

    {
      assert!(!sfa.member(&"abe".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"bc".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"xxxxx".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"".chars().collect::<Vec<char>>()[..]));
    }
  }

  #[test]
  fn reg_sfa_or() {
    let reg = Regex::parse("(abc)|(kkk)|_").unwrap();
    let sfa = reg.to_sym_fa::<Rc<State>>();

    {
      assert!(sfa.member(&"abc".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.member(&"kkk".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.member(&"d".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.member(&"x".chars().collect::<Vec<char>>()[..]));
    }

    {
      assert!(!sfa.member(&"ab".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"kk".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"xxxxx".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"abcd".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"kkx".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"".chars().collect::<Vec<char>>()[..]));
    }
  }

  #[test]
  #[ignore]
  fn reg_sfa_inter() {
    let reg = Regex::parse("(_*)abc(abc*)(_*)")
      .unwrap()
      .inter(Regex::parse("(x*)(abc*)(y*)").unwrap());
    let sfa = reg.to_sym_fa::<Rc<State>>();

    {
      assert!(sfa.member(&"abc".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.member(&"xxabc".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.member(&"abcyyy".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.member(&"xxxabcabcyyy".chars().collect::<Vec<char>>()[..]));
    }

    {
      assert!(!sfa.member(&"ab".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"xabcabcaby".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"xxxxx".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"abcd".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"yyyy".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.member(&"".chars().collect::<Vec<char>>()[..]));
    }

    unreachable!()
  }

  #[test]
  fn reg_sfa() {
    let reg = Regex::parse("a*b(c|d)a").unwrap();
    let sfa = reg.to_sym_fa::<Rc<State>>();

    assert!(sfa.member(&"aaabca".chars().collect::<Vec<char>>()[..]));
    assert!(sfa.member(&"bca".chars().collect::<Vec<char>>()[..]));
    assert!(sfa.member(&"aaabda".chars().collect::<Vec<char>>()[..]));
    assert!(!sfa.member(&"aaa".chars().collect::<Vec<char>>()[..]));
    assert!(!sfa.member(&"zzz".chars().collect::<Vec<char>>()[..]));
    assert!(!sfa.member(&"axda".chars().collect::<Vec<char>>()[..]));
  }
}
