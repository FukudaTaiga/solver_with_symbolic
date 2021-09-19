pub trait Recognizable<T> {
  fn recognize(&self, input: T) -> bool;
}