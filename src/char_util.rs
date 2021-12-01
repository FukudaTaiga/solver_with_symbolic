use std::{
  fmt::Debug,
  hash::Hash
};

pub trait FromChar: Debug + PartialEq + Eq + PartialOrd + Ord + Clone + Copy + Hash {
  fn from_char(c: char) -> Self;
}
impl FromChar for char {
  fn from_char(c: char) -> Self {
    c
  }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum CharWrap {
  Char(char),
  Separator
}
impl FromChar for CharWrap {
  fn from_char(c: char) -> Self {
    CharWrap::Char(c)
  }
}