pub mod recognizable;
pub mod regex;
pub mod symbolic_automata;

#[cfg(test)]
pub mod tests {
  use super::recognizable::Recognizable;
  use super::regex::Regex;
  use crate::tests::helper::*;
  use crate::state::StateMachine;
  use std::rc::Rc;

  type Reg = Regex<char>;

  #[test]
  fn reg_sfa_all() {
    let reg = Reg::all();
    let reg2 = Reg::all().star();
    let sfa = reg.to_sym_fa::<Rc<StateImpl>>();
    let sfa2 = reg2.to_sym_fa::<Rc<StateImpl>>();

    {
      assert!(sfa.member(&chars("a")));
      assert!(sfa.member(&chars("x")));
      assert!(sfa.member(&chars("$")));
      assert!(sfa2.member(&chars("cdsnjcdskcnsdjk")));
      assert!(sfa2.member(&chars("xxxxxxx")));
      assert!(sfa2.member(&chars(":cdskoapcd")));
      assert!(sfa2.member(&chars("")));
    }

    {
      assert!(!sfa.member(&chars("")));
      assert!(!sfa.member(&chars("ax")));
    }
  }

  #[test]
  fn reg_sfa_epsilon() {
    let reg = Reg::epsilon();
    let reg2 = Reg::seq("avc").concat(Reg::epsilon());
    let sfa = reg.to_sym_fa::<Rc<StateImpl>>();
    let sfa2 = reg2.to_sym_fa::<Rc<StateImpl>>();

    {
      assert!(sfa.member(&chars("")));
      assert!(sfa2.member(&chars("avc")));
    }

    {
      assert!(!sfa.member(&chars("ab")));
      assert!(!sfa2.member(&chars("av")));
      assert!(!sfa.member(&chars("xxxxx")));
      assert!(!sfa.member(&chars("avcs")));
    }
  }

  #[test]
  fn reg_sfa_star() {
    let reg = Reg::element('w')
      .concat(Reg::element('a').star())
      .concat(Reg::element('x'))
      .concat(Reg::element('b').star())
      .concat(Reg::element('y'))
      .concat(Reg::element('c').star())
      .concat(Reg::element('z'));
    let sfa = reg.to_sym_fa::<Rc<StateImpl>>();

    {
      assert!(sfa.member(&chars("waaaxbyccccz")));
      assert!(sfa.member(&chars("waaaxyccccz")));
      assert!(sfa.member(&chars("wxbyccccz")));
      assert!(sfa.member(&chars("waaaxbyz")));
      assert!(sfa.member(&chars("waaaxyz")));
      assert!(sfa.member(&chars("wxbyz")));
      assert!(sfa.member(&chars("wxyccccz")));
      assert!(sfa.member(&chars("wxyz")));
    }

    {
      assert!(!sfa.member(&chars("aabbcc")));
      assert!(!sfa.member(&chars("waxbyc")));
      assert!(!sfa.member(&chars("axbycz")));
      assert!(!sfa.member(&chars("waxbcz")));
      assert!(!sfa.member(&chars("wabycz")));
    }
  }

  #[test]
  fn reg_sfa_concat() {
    let reg = Reg::all()
      .star()
      .concat(Reg::seq("abc").plus())
      .concat(Reg::all().star());
    let sfa = reg.to_sym_fa::<Rc<StateImpl>>();

    {
      assert!(sfa.member(&chars("xxzxabcde")));
      assert!(sfa.member(&chars("abc")));
      assert!(sfa.member(&chars("xxxzabcabcabcxe")));
    }

    {
      assert!(!sfa.member(&chars("abe")));
      assert!(!sfa.member(&chars("bc")));
      assert!(!sfa.member(&chars("xxxxx")));
      assert!(!sfa.member(&chars("")));
    }
  }

  #[test]
  fn reg_sfa_or() {
    let reg = Reg::seq("abc").or(Reg::seq("kkk")).or(Reg::all());
    let sfa = reg.to_sym_fa::<Rc<StateImpl>>();

    {
      assert!(sfa.member(&chars("abc")));
      assert!(sfa.member(&chars("kkk")));
      assert!(sfa.member(&chars("d")));
      assert!(sfa.member(&chars("x")));
    }

    {
      assert!(!sfa.member(&chars("ab")));
      assert!(!sfa.member(&chars("kk")));
      assert!(!sfa.member(&chars("xxxxx")));
      assert!(!sfa.member(&chars("abcd")));
      assert!(!sfa.member(&chars("kkx")));
      assert!(!sfa.member(&chars("")));
    }
  }

  #[test]
  fn reg_sfa_inter() {
    let reg1 = Reg::all()
      .star()
      .concat(Reg::seq("abc").plus())
      .concat(Reg::all().star());
    let reg2 = Reg::element('x')
      .star()
      .concat(Reg::seq("abc").star())
      .concat(Reg::element('y').star());
    let reg = reg1.inter(reg2);
    let sfa = reg.to_sym_fa::<Rc<StateImpl>>();

    eprintln!("t: {:?}", sfa.transition());
    eprintln!("i: {:?}", sfa.initial_state());
    eprintln!("f: {:?}", sfa.final_set());
    
    {
      assert!(sfa.member(&chars("abc")));
      assert!(sfa.member(&chars("xxabc")));
      assert!(sfa.member(&chars("abcyyy")));
      assert!(sfa.member(&chars("xxxabcabcyyy")));
    }

    {
      assert!(!sfa.member(&chars("ab")));
      assert!(!sfa.member(&chars("xabcabcaby")));
      assert!(!sfa.member(&chars("xxxxx")));
      assert!(!sfa.member(&chars("abcd")));
      assert!(!sfa.member(&chars("yyyy")));
      assert!(!sfa.member(&chars("")));
    }
  }

  #[test]
  fn reg_sfa() {
    let reg = Reg::element('a')
      .star()
      .concat(Reg::element('b'))
      .concat(Reg::element('c').or(Reg::element('d')))
      .concat(Reg::element('a'));
    let sfa = reg.to_sym_fa::<Rc<StateImpl>>();

    assert!(sfa.member(&chars("aaabca")));
    assert!(sfa.member(&chars("bca")));
    assert!(sfa.member(&chars("aaabda")));
    assert!(!sfa.member(&chars("aaa")));
    assert!(!sfa.member(&chars("zzz")));
    assert!(!sfa.member(&chars("axda")));
  }
}
