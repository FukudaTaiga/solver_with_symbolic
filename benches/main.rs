#![feature(test)]
extern crate test;
extern crate solver_with_symbolic;

#[cfg(test)]
mod benches {
  use super::*;
  use test::Bencher;

  #[bench]
  fn dumm(b: &mut Bencher) {
    let input = r#"
    (declare-const x0 String)
    (declare-const x1 String)
    (declare-const x2 String)
    (assert (= x1 (str.++ x0 (str.reverse x0))))
    (assert (= x2
      (str.++ x1
        (str.replaceallre x0
          (str.to.re "abc") "xyz"
        ) x1
      )
    ))
    (assert (str.in.re x1 (re.+ (str.to.re "ab"))))
    (assert (str.in.re x2 (re.* (str.to.re "xyz"))))
    (check-sat)
    (get-model)
    "#;
    let smt2 = solver_with_symbolic::parse(input);

    b.iter(move || solver_with_symbolic::check_sat(smt2.clone()));
  }
}