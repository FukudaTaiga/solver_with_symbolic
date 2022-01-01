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

pub mod extention {
  use std::{collections::HashMap, default::Default, hash::Hash, iter::Extend};

  pub trait HashMapExt {
    type Key: Eq + Hash;
    type Value;

    fn insert_with_check(&mut self, key: Self::Key, values: impl IntoIterator<Item = Self::Value>);

    fn merge(&mut self, other: Self);
  }
  impl<K, V, Collection> HashMapExt for HashMap<K, Collection>
  where
    K: Eq + Hash,
    Collection: IntoIterator<Item = V> + Extend<V> + Default,
  {
    type Key = K;
    type Value = V;

    fn insert_with_check(&mut self, key: Self::Key, values: impl IntoIterator<Item = Self::Value>) {
      let vec = self.entry(key).or_default();
      vec.extend(values);
    }

    fn merge(&mut self, other: Self) {
      for (key, values_) in other.into_iter() {
        let values = self.entry(key).or_default();
        values.extend(values_);
      }
    }
  }
}
