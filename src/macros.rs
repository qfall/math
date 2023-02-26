/// Implements the [From] trait for a given type. It requires an already written conversion function (e.g. form_i64).
///
/// Input parameters:
/// * source_type: the source identifier (e.g. i64, u32,...).
/// * destination_type: the destination identifier (e.g. Z, MatZ).
/// * function: The function that needs to be called for the conversion (e.g. Z::from_i64)
///
/// Output:
/// * Implementation code for the [From] Trait with signature (`impl From<*source_type*> for *destination_type*`)
macro_rules! from_trait {
    ($source_type:ident, $destination_type:ident, $function:expr) => {
        impl From<$source_type> for $destination_type {
            #[doc=stringify!(Convert [$source_type] to [$destination_type] using [$function].)]
            fn from(value: $source_type) -> $destination_type {
                $function(value)
            }
        }
    };
}

pub(crate) use from_trait;
