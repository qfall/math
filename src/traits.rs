pub trait Evaluate<U, V> {
    fn evaluate<T: Into<U>>(&self, value: T) -> V;
}
