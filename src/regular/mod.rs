pub mod recognizable;
pub mod regex;
pub mod symbolic_automata;

#[cfg(test)]
mod tests {
  use super::recognizable::Recognizable;
  use super::regex::Regex;

  #[test]
  fn reg_sfa_all_test() {
    let reg = Regex::new("_").unwrap();
    let reg2 = Regex::new("_*").unwrap();
    let sfa = reg.to_sym_fa();
    let sfa2 = reg2.to_sym_fa();
    println!("regex:\n{:#?}", reg2);
    println!("sfa:\n{:#?}", sfa2);

    {
      assert!(sfa.run(&"a".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.run(&"x".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.run(&"$".chars().collect::<Vec<char>>()[..]));
      assert!(sfa2.run(&"cdsnjcdskcnsdjk".chars().collect::<Vec<char>>()[..]));
      assert!(sfa2.run(&"xxxxxxx".chars().collect::<Vec<char>>()[..]));
      assert!(sfa2.run(&":cdskoapcd".chars().collect::<Vec<char>>()[..]));
    }

    {
      assert!(!sfa.run(&"".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"ax".chars().collect::<Vec<char>>()[..]));
    }
  }

  #[test]
  fn reg_sfa_eps_test() {
    let reg = Regex::new("!*").unwrap();
    let reg2 = Regex::new("avc(!*)").unwrap();
    let sfa = reg.to_sym_fa();
    let sfa2 = reg2.to_sym_fa();
    println!("regex:\n{:#?}", reg);
    println!("sfa:\n{:#?}", sfa);

    {
      assert!(sfa.run(&"".chars().collect::<Vec<char>>()[..]));
      assert!(sfa2.run(&"avc".chars().collect::<Vec<char>>()[..]));
    }

    {
      assert!(!sfa.run(&"ab".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa2.run(&"av".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"xxxxx".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"avcs".chars().collect::<Vec<char>>()[..]));
    }
  }

  #[test]
  fn reg_sfa_concat_test() {
    let reg = Regex::new("abc_e").unwrap();
    let sfa = reg.to_sym_fa();
    println!("regex:\n{:#?}", reg);
    println!("sfa:\n{:#?}", sfa);

    {
      assert!(sfa.run(&"abcde".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.run(&"abcke".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.run(&"abcxe".chars().collect::<Vec<char>>()[..]));
    }

    {
      assert!(!sfa.run(&"abce".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"abc".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"xxxxx".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"".chars().collect::<Vec<char>>()[..]));
    }
  }

  #[test]
  fn reg_sfa_or_test() {
    let reg = Regex::new("(abc)|(kkk)|_").unwrap();
    let sfa = reg.to_sym_fa();
    println!("regex:\n{:#?}", reg);
    println!("sfa:\n{:#?}", sfa);

    {
      assert!(sfa.run(&"abc".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.run(&"kkk".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.run(&"d".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.run(&"x".chars().collect::<Vec<char>>()[..]));
    }

    {
      assert!(!sfa.run(&"ab".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"kk".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"xxxxx".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"abcd".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"kkx".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"".chars().collect::<Vec<char>>()[..]));
    }
  }

  #[test]
  fn reg_sfa_star_test() {
    let reg = Regex::new("(a*)(b*)(c*)").unwrap();
    let sfa = reg.to_sym_fa();
    println!("regex:\n{:#?}", reg);
    println!("sfa:\n{:#?}", sfa);

    {
      assert!(sfa.run(&"aaabcccc".chars().collect::<Vec<char>>()[..]));

      assert!(sfa.run(&"aaacccc".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.run(&"bcccc".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.run(&"aaab".chars().collect::<Vec<char>>()[..]));

      assert!(sfa.run(&"aaa".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.run(&"b".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.run(&"cccc".chars().collect::<Vec<char>>()[..]));

      assert!(sfa.run(&"".chars().collect::<Vec<char>>()[..]));
    }

    {
      assert!(!sfa.run(&"kcd".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"abca".chars().collect::<Vec<char>>()[..]));
    }
  }

  #[test]
  fn reg_to_sfa_test() {
    let reg = Regex::new("a*b(c|d)a").unwrap();
    let sfa = reg.to_sym_fa();
    println!("regex:\n{:#?}", reg);
    println!("sfa:\n{:#?}", sfa);

    assert!(sfa.run(&"aaabca".chars().collect::<Vec<char>>()[..]));
    assert!(sfa.run(&"bca".chars().collect::<Vec<char>>()[..]));
    assert!(sfa.run(&"aaabda".chars().collect::<Vec<char>>()[..]));
    assert!(!sfa.run(&"aaa".chars().collect::<Vec<char>>()[..]));
    assert!(!sfa.run(&"zzz".chars().collect::<Vec<char>>()[..]));
    assert!(!sfa.run(&"axda".chars().collect::<Vec<char>>()[..]));
  }
}
