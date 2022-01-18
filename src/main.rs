extern crate solver_with_symbolic;

use std::{env, fs::File, io::Read};

/**
 * TODO
 * 1. fix boolean_algebra::Predicate::reduce()
 * 2. consider minimization algorism (Hopcroft, Moore, Paige-Tarjan's)
 */
fn main() {
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
  
  println!("{:?}", solver_with_symbolic::run(&input));
}
