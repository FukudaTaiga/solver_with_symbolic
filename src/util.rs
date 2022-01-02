use std::{fmt::Debug, hash::Hash};

pub trait Domain: Debug + Eq + Ord + Clone + Hash + From<char> {
  fn separator() -> Self;
}
impl Domain for char {
  fn separator() -> Self {
    '#'
  }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum CharWrap {
  Char(char),
  Separator,
}
impl From<char> for CharWrap {
  fn from(a: char) -> Self {
    CharWrap::Char(a)
  }
}
impl Domain for CharWrap {
  fn separator() -> Self {
    CharWrap::Separator
  }
}

pub(crate) mod extention {
  use std::{collections::HashMap, default::Default, hash::Hash, iter::Extend};

  pub(crate) trait MultiMap {
    type Key: Eq + Hash;
    type Value;

    fn insert_with_check(&mut self, key: Self::Key, values: impl IntoIterator<Item = Self::Value>);

    fn merge(&mut self, other: Self);
  }
  impl<K, V, Collection> MultiMap for HashMap<K, Collection>
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

  pub(crate) trait ImmutableValueMap {
    type Key: Eq + Hash;
    type Value;

    fn safe_insert(&mut self, key: Self::Key, value: Self::Value);
  }
  impl<K: Eq + Hash, V> ImmutableValueMap for HashMap<K, V> {
    type Key = K;
    type Value = V;

    fn safe_insert(&mut self, key: Self::Key, value: Self::Value) {
      assert!(self.insert(key, value).is_none());
    }
  }
}
