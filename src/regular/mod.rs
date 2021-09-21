pub mod regex;
pub mod symbolic_automata;
pub mod recognizable;

#[cfg(test)]
mod tests {
  use super::recognizable::Recognizable;
  use super::regex::{Regex};

  #[test]
  //#[ignore]
  fn reg_to_sfa_test() {
      let reg = Regex::new("a*b(c|d)a").unwrap();
      println!("regex:\n{:#?}", reg);
      let sfa = reg.to_sym_fa();
      println!("sfa:\n{:#?}", sfa);

      assert!(sfa.run(&"aaabca".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.run(&"bca".chars().collect::<Vec<char>>()[..]));
      assert!(sfa.run(&"aaabda".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"aaa".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"zzz".chars().collect::<Vec<char>>()[..]));
      assert!(!sfa.run(&"axda".chars().collect::<Vec<char>>()[..]));
  }
}