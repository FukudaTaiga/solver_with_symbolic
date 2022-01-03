pub mod recognizable;
pub mod regex;
pub mod symbolic_automata;

/* for readability */
pub(crate) mod macros {
  macro_rules! sfa {
    ( { $( $state:ident ),+ },
      {
        -> $initial:ident,
        $( ($source:ident, $predicate:expr) -> [$($target:ident),*] ),*
      },
      { $( $final_state:ident ),* }
    ) => {{
      use crate::regular::symbolic_automata::SymFA;

      let mut states = HashSet::new();
      $( let $state = S::new(); states.insert(S::clone(&$state)); )+
      let transition = HashMap::from([
        $( (( S::clone(&$source), $predicate), vec![$(S::clone(&$target)),*]) )*
      ]);
      let final_states = HashSet::from([$( S::clone(&$final_state) ),*]);
      SymFA::new(states, $initial, final_states, transition)
    }};
  }

  pub(crate) use sfa;
}

#[cfg(test)]
mod tests {
  use super::regex::Regex;
  use crate::tests::helper::*;

  type Reg = Regex<char>;

  #[test]
  fn reg_sfa_all() {
    let all = Reg::all().to_sym_fa::<StateImpl>();
    let universe = Reg::all().star().to_sym_fa::<StateImpl>();
    assert!(all.run(&chars("a")));
    assert!(all.run(&chars("x")));
    assert!(all.run(&chars("$")));
    assert!(universe.run(&chars("")));
    assert!(universe.run(&chars("cdsnjcdskcnsdjk")));
    assert!(universe.run(&chars("xxxxxxx")));
    assert!(universe.run(&chars(":cdskoapcd")));

    assert!(!all.run(&chars("")));
    assert!(!all.run(&chars("ax")));
    assert!(!all.run(&chars("cdsnjcdskcnsdjk")));
    assert!(!all.run(&chars("xxxxxxx")));
  }

  #[test]
  fn reg_sfa_epsilon() {
    let sfa = Reg::epsilon().to_sym_fa::<StateImpl>();

    assert!(sfa.run(&chars("")));

    assert!(!sfa.run(&chars("ab")));
    assert!(!sfa.run(&chars("xxxxx")));
    assert!(!sfa.run(&chars("avcs")));
  }

  #[test]
  fn epsilon_has_no_effect_with_concat() {
    let reg = Reg::seq("avc");
    let orig = reg.clone().to_sym_fa::<StateImpl>();
    let concat = reg.concat(Reg::epsilon()).to_sym_fa::<StateImpl>();

    assert!(orig.run(&chars("avc")));
    assert!(concat.run(&chars("avc")));

    assert!(!orig.run(&chars("")));
    assert!(!concat.run(&chars("")));
    assert!(!orig.run(&chars("av")));
    assert!(!concat.run(&chars("av")));
    assert!(!orig.run(&chars("aavc")));
    assert!(!concat.run(&chars("aavc")));
  }

  #[test]
  fn reg_sfa_star() {
    let sfa = Reg::seq("abc").star().to_sym_fa::<StateImpl>();

    for i in 0..10 {
      assert!(sfa.run(&chars(&"abc".repeat(i))));
    }

    assert!(!sfa.run(&chars("abca")));
    assert!(!sfa.run(&chars("abbc")));
    assert!(!sfa.run(&chars("aabc")));
    assert!(!sfa.run(&chars("xyz")));
  }

  #[test]
  fn reg_sfa_concat() {
    let reg = Reg::all()
      .star()
      .concat(Reg::seq("abc").plus())
      .concat(Reg::all().star());
    let sfa = reg.to_sym_fa::<StateImpl>();

    assert!(sfa.run(&chars("xxzxabcde")));
    assert!(sfa.run(&chars("abc")));
    assert!(sfa.run(&chars("xxxzabcabcabcxe")));

    assert!(!sfa.run(&chars("abe")));
    assert!(!sfa.run(&chars("bc")));
    assert!(!sfa.run(&chars("xxxxx")));
    assert!(!sfa.run(&chars("")));
  }

  #[test]
  fn reg_sfa_or() {
    let reg = Reg::seq("abc")
      .or(Reg::seq("kkk"))
      .or(Reg::all())
      .or(Reg::epsilon());
    let sfa = reg.to_sym_fa::<StateImpl>();

    assert!(sfa.run(&chars("abc")));
    assert!(sfa.run(&chars("kkk")));
    assert!(sfa.run(&chars("d")));
    assert!(sfa.run(&chars("x")));
    assert!(!sfa.run(&chars("")));

    assert!(!sfa.run(&chars("ab")));
    assert!(!sfa.run(&chars("kk")));
    assert!(!sfa.run(&chars("xxxxx")));
    assert!(!sfa.run(&chars("abcd")));
    assert!(!sfa.run(&chars("kkx")));
  }

  #[test]
  fn reg_sfa_inter_simple() {
    let reg1 = Reg::element('a')
      .or(Reg::element('s'))
      .or(Reg::element('d'));
    let reg2 = Reg::element('b')
      .or(Reg::element('s'))
      .or(Reg::element('d'));
    let reg = reg1.inter(reg2);
    let sfa = reg.to_sym_fa::<StateImpl>();

    assert!(sfa.run(&chars("s")));
    assert!(sfa.run(&chars("d")));

    assert!(!sfa.run(&chars("")));
    assert!(!sfa.run(&chars("a")));
    assert!(!sfa.run(&chars("b")));
    assert!(!sfa.run(&chars("x")));
    assert!(!sfa.run(&chars("asdb")));
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
    let sfa = reg.to_sym_fa::<StateImpl>();

    assert!(sfa.run(&chars("abc")));
    assert!(sfa.run(&chars("xxabc")));
    assert!(sfa.run(&chars("abcyyy")));
    assert!(sfa.run(&chars("xxxabcabcyyy")));

    assert!(!sfa.run(&chars("ab")));
    assert!(!sfa.run(&chars("xabcabcaby")));
    assert!(!sfa.run(&chars("xxxxx")));
    assert!(!sfa.run(&chars("abcd")));
    assert!(!sfa.run(&chars("yyyy")));
    assert!(!sfa.run(&chars("")));
  }

  #[test]
  fn reg_sfa_not() {
    let sfa = Reg::element('a')
      .or(Reg::element('b'))
      .not()
      .to_sym_fa::<StateImpl>();

    assert!(sfa.run(&chars("")));
    assert!(sfa.run(&chars("c")));
    assert!(sfa.run(&chars("xxxx")));
    assert!(sfa.run(&chars("ab")));
    assert!(sfa.run(&chars("ba")));

    assert!(!sfa.run(&chars("a")));
    assert!(!sfa.run(&chars("b")));
  }
}
