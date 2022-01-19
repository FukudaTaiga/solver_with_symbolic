pub mod recognizable;
pub mod regex;
pub mod symbolic_automata;

/* for readability */
pub(crate) mod macros {
  macro_rules! sfa {
    ( { $( $state:ident ),+ },
      {
        -> $initial:ident
        $(, ($source:ident, $predicate:expr) -> [$($target:ident),*] )*
      },
      { $( $final_state:ident ),* }
    ) => {{
      use crate::regular::symbolic_automata::SymFa;

      let mut states = HashSet::new();
      $( let $state = S::new(); states.insert(S::clone(&$state)); )+
      let transition = HashMap::from([
        $( (( S::clone(&$source), $predicate), vec![$(S::clone(&$target)),*]) ),*
      ]);
      let final_states = HashSet::from([$( S::clone(&$final_state) ),*]);
      SymFa::new(states, $initial, final_states, transition)
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
    let all = Reg::all().to_sfa::<StateImpl>();
    let universe = Reg::all().star().to_sfa::<StateImpl>();
    for accept in ["a", "x", "$"] {
      assert!(run!(all, [accept]));
    }
    for case in ["", "cdsnjcdskcnsdjk", "xxxxxxx", ":cdskoapcd"] {
      assert!(run!(universe, [case]));
      assert!(!run!(all, [case]));
    }
  }

  #[test]
  fn reg_sfa_epsilon() {
    let sfa = Reg::epsilon().to_sfa::<StateImpl>();

    assert!(run!(sfa, [""]));

    for reject in ["ab", "xxxxxxx", "avcs"] {
      assert!(!run!(sfa, [reject]));
    }
  }

  #[test]
  fn epsilon_has_no_effect_with_concat() {
    let reg = Reg::seq("avc");
    let orig = reg.clone().to_sfa::<StateImpl>();
    let concat = reg.concat(Reg::epsilon()).to_sfa::<StateImpl>();

    assert!(run!(orig, ["avc"]));
    assert!(run!(concat, ["avc"]));

    for reject in ["", "av", "aavc"] {
      assert!(!run!(orig, [reject]));
      assert!(!run!(concat, [reject]));
    }
  }

  #[test]
  fn reg_sfa_star() {
    let sfa = Reg::seq("abc").star().to_sfa::<StateImpl>();

    for i in 0..10 {
      assert!(run!(sfa, ["abc".repeat(i)]));
    }
    for reject in ["abca", "abbc", "aabc", "xyz"] {
      assert!(!run!(sfa, [reject]));
    }
  }

  #[test]
  fn reg_sfa_plus() {
    let sfa = Reg::seq("abc").plus().to_sfa::<StateImpl>();

    for i in 0..10 {
      assert!(run!(sfa, ["abc".repeat(i)]) ^ (i == 0));
    }
    for reject in ["abca", "abbc", "aabc", "xyz"] {
      assert!(!run!(sfa, [reject]));
    }
  }

  #[test]
  fn reg_sfa_concat() {
    let sfa = Reg::all()
      .star()
      .concat(Reg::seq("abc").plus())
      .concat(Reg::all().star())
      .to_sfa::<StateImpl>();

    for accept in ["xxzxabcde", "abc", "xxxzabcabcabcxe"] {
      assert!(run!(sfa, [accept]));
    }
    for reject in ["abe", "bc", "xxxxx", ""] {
      assert!(!run!(sfa, [reject]));
    }
  }

  #[test]
  fn reg_sfa_or() {
    let sfa = Reg::seq("abc")
      .or(Reg::seq("kkk"))
      .or(Reg::all())
      .or(Reg::epsilon())
      .to_sfa::<StateImpl>();

    for accept in ["abc", "kkk", "d", "x", ""] {
      assert!(run!(sfa, [accept]));
    }
    for reject in ["ab", "kk", "xxxxxx", "abcd", "kkx"] {
      assert!(!run!(sfa, [reject]));
    }
  }

  #[test]
  fn reg_sfa_inter_simple() {
    let reg1 = Reg::element('a')
      .or(Reg::element('s'))
      .or(Reg::element('d'));
    let reg2 = Reg::element('b')
      .or(Reg::element('s'))
      .or(Reg::element('d'));
    let sfa = reg1.inter(reg2).to_sfa::<StateImpl>();

    for accept in ["s", "d"] {
      assert!(run!(sfa, [accept]));
    }
    for reject in ["", "a", "b", "x", "asdb"] {
      assert!(!run!(sfa, [reject]));
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
    let sfa = reg.to_sfa::<StateImpl>();

    for accept in ["abc", "xxabc", "abcyyy", "xxxabcabcyyy"] {
      assert!(run!(sfa, [accept]));
    }
    for reject in ["ab", "xabcabcaby", "xxxxx", "abcd", "yyyyy", ""] {
      assert!(!run!(sfa, [reject]));
    }
  }

  #[test]
  fn reg_sfa_not() {
    let sfa = Reg::element('a')
      .or(Reg::element('b'))
      .not()
      .to_sfa::<StateImpl>();

    for accept in ["", "c", "xxxxxx", "ab", "ba"] {
      assert!(run!(sfa, [accept]));
    }
    for reject in ["a", "b"] {
      assert!(!run!(sfa, [reject]));
    }
  }
}
