use thiserror::Error;

#[derive(Error, Debug)]
pub enum MathError {
    /// parse string error
    #[error("invalid string input {0}")]
    InvalidStringInput(#[from] ParseError),
}
