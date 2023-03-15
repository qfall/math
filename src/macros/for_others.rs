/// Implements the [`SetCoefficient`](crate::traits::SetCoefficient) for [`*type*`] using the conversions from the
/// [`*bridge_type*`] for
/// [`*type*`].
///
/// Parameters:
/// - source_type: the type of the input (e.g. [`i32`], [`i64`])
/// - bridge_type: the type in which the input is converted
/// - type: the type for which the [`SetCoefficient`](crate::traits::SetCoefficient) is implemented (e.g. [`PolyOverZ`](crate::integer::PolyOverZ), [`PolyOverQ`](crate::rational::PolyOverQ))
///
/// Returns the owned Implementation code for the specified
/// trait with the signature:
///
/// ```impl *specified trait*<*&source_type*> for *type*```
macro_rules! implement_for_others_set_coeff {
    ($source_type:ident, $bridge_type:ident, $type:ident) => {
        impl SetCoefficient<$source_type> for $type {
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::set_coeff`]. Implicitly converts [`" $source_type "`] into [`" $bridge_type "`]."]
            fn set_coeff(
                &mut self,
                coordinate: impl TryInto<i64> + Display + Copy,
                value: $source_type,
            ) -> Result<(), MathError> {
                self.set_coeff(coordinate, $bridge_type::from(value))
            }
            }
        }
    };
}

pub(crate) use implement_for_others_set_coeff;
