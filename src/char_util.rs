use std::{fmt::Debug, hash::Hash};

pub trait FromChar: Debug + PartialEq + Eq + PartialOrd + Ord + Clone + Hash {
  fn from_char(c: char) -> Self;
  fn separator() -> Self;
}
impl FromChar for char {
  fn from_char(c: char) -> Self {
    c
  }

  fn separator() -> Self {
    '#'
  }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum CharWrap {
  Char(char),
  Separator,
}
impl FromChar for CharWrap {
  fn from_char(c: char) -> Self {
    CharWrap::Char(c)
  }

  fn separator() -> Self {
    CharWrap::Separator
  }
}
