pub trait Recognizable<T> {
  fn run(&self, input: &[T]) -> bool;
}