mod boolean_algebra;
mod char_util;
pub mod regular;
pub mod smt2;
mod state;
pub mod transducer;

use char_util::CharWrap;
use smt2::Smt2;
use state::State;
use std::{env, fs::File, io::Read, rc::Rc};

pub fn run() {
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

  let smt2 = Smt2::<CharWrap, Rc<State>>::parse(&input).unwrap();

  println!("{:?}", smt2);
}
