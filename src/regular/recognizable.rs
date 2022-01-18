pub trait Recognizable<T> {
    fn member(&self, input: &[T]) -> bool;
}
