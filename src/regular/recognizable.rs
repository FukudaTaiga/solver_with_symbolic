pub trait Recognizable<T> {
  fn recognize(&self, input: Vec<T>) -> bool;
}