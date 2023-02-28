/// Implements the [From] trait for a given type. It requires an already written
/// conversion function (e.g. [Z::from_i64()](crate::integer::Z::from_i64())).
///
/// Input parameters:
/// - source_type: the source identifier (e.g. [i64], [u32], ...).
/// - destination_type: the destination identifier 
///   (e.g. [Z](crate::integer::Z), [MatZ](crate::integer::MatZ)).
/// - function: The function that needs to be called for the conversion
///   (e.g. [Z::from_i64()])
/// Returns the Implementation code for the [From] Trait with the signature:
/// ```impl From<*source_type*> for *destination_type*```
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

/// Create a `from_<source_type>` function for `<destination_type>`.
///
/// The `from_<source_type>` function is just a wrapper for
/// `<function>(value as <bridge_type>)`.
///
/// This macro is intended to be used to quickly create implementations for
/// similar types that can be casted into each other.
/// For example, for [i8], [i16], and [i32] given a working conversion for [i64].
///
/// A short documentation is automatically included with the pattern:
/// > "Convert <source_type> to <destination_type> using < function>."
///
/// The macro is supposed to be used inside of an `impl` block for the destination type.
///
/// Input parameters:
/// - source_type: The source identifier (e.g. [i64], [u32], ...).
/// - bridge_type: Type used for casting before calling the function.
/// - destination_type: Return type of the generated function
///   (e.g. [Z](crate::integer::Z), [MatZ](crate::integer::MatZ)).
/// - function: The function that needs to be called for the conversion
///   (e.g. [Z::from_i64()]).
/// Returns the Implementation code for the function `from_<source_type>`.
///
/// # Example
/// ```ignore
/// use math::macros;
/// impl Z {
///     pub fn from_i64(value: i64) -> Self { ... }
///
///     macros::from_type!(i32, i64, Z, Z::from_i64);
/// }
/// ```
/// check out the source code of [Z::from_i32] for the full example.
macro_rules! from_type {
    ($source_type:ident, $bridge_type:ident, $destination_type:ident, $( $function:ident )::*) => {
        // This macro could be modified to create it's own `impl` block and also
        // automatically create the corresponding [From] trait. However, this
        // also adds a new `impl` block in the documentation. This is discussed in the
        // rust-lang issues [82408](https://github.com/rust-lang/rust/issues/82408) 
        // and [52563](https://github.com/rust-lang/rust/issues/52563).
        // Once this is resolved, it can be implemented by uncommenting the following
        // comments in this block.

        // impl $destination_type {
            paste::paste! {
                #[doc = "Convert [" $source_type "] to [" $destination_type "] using [" $($function)"::"* "]."]
                pub fn [<from_ $source_type>](value: $source_type) -> $destination_type {
                    $($function)::*(value as $bridge_type)
                }
            }
        // }
        // paste::paste! {
        //     macros::from_trait!(
        //         $source_type,
        //         $destination_type,
        //         $destination_type::[<from_ $source_type>]
        //     );
        // }
    };
}

pub(crate) use from_type;
