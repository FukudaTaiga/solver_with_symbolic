extern crate solver_with_symbolic;

use std::{env, fs::File, io::Read};

/**
 * TODO
 * 1. consider minimization algorism (Hopcroft, Moore, Paige-Tarjan's)
 */
fn main() {
  let mut args = env::args();
  args.next();
  let mut input = String::new();
  let mut is_file_given = false;

  for arg in args {
    if arg.starts_with("--") {
    } else if arg.starts_with("-") {
    } else {
      let read_result = File::open(arg).and_then(|mut file| file.read_to_string(&mut input));

      if read_result.is_err() {
        println!("failed to read file for {}", read_result.unwrap_err());
        return;
      } else {
        is_file_given = true;
      }
    }
  }

  if is_file_given {
    solver_with_symbolic::run(&input);
  } else {
    println!("no smt2 file given.");
  }
}
