/// Implements the [`*trait*`] for [`*type*`] using a FLINT function.
///
/// Parameters:
/// - meta: meta data used for documentation (e.g. doc="...")
/// - trait: the trait that is implemented (e.g. [`Add`], [`Sub`], ...).
/// - trait_function: the function the trait implements
/// (e.g. add for [`Add`], ...).
/// - type: the type the trait is implemented for (e.g. [`Z`], [`Q`])
/// - function: The function that needs to be called
/// (e.g. [`flint_sys::fmpz::fmpz_add`]).
/// - default: the default value that is taken for the output for the function.
/// - attribute_name: the name of the attribute of the type, that is needed for
/// the computation.
///
/// Returns the standard and borrowed Implementation code for the [`*trait*`]
/// trait with the signatures:
///
/// ```impl *trait*<*type*> for *type*```
///
/// ```impl *trait*<&*type*> for &*type*```
///
/// ```impl *trait*<*type*> for &*type*```
///
/// ```impl *trait*<&*type*> for *type*```
macro_rules! arithmetic_trait {
    ($meta:meta,$trait:ident, $trait_function:ident, $type:ident, $function:expr, $default:expr, $attribute_name:ident) => {
        impl $trait for &$type {
            type Output = $type;
            #[$meta]
            fn $trait_function(self, other: Self) -> Self::Output {
                let mut out = $default;
                unsafe {
                    $function(&mut out, &self.$attribute_name, &other.$attribute_name);
                }
                $type {
                    $attribute_name: out,
                }
            }
        }

        impl $trait for $type {
            type Output = $type;

            fn $trait_function(self, other: Self) -> Self::Output {
                (&self).$trait_function(&other)
            }
        }

        impl $trait<$type> for &$type {
            type Output = $type;

            fn $trait_function(self, other: $type) -> Self::Output {
                self.$trait_function(&other)
            }
        }

        impl $trait<&$type> for $type {
            type Output = $type;

            fn $trait_function(self, other: &Self) -> Self::Output {
                (&self).$trait_function(other)
            }
        }
    };
}

pub(crate) use arithmetic_trait;

/// Implements the [`*trait*`] for [`*type*`] using the [`*trait*`] for
/// [`&*type*`].
///
/// Parameters:
/// - trait: the trait that is implemented (e.g. [`Add`], [`Sub`], ...).
/// - trait_function: the function the trait implements
/// (e.g. add for [`Add`], ...).
/// - type: the type the trait is implemented for (e.g. [`Z`], [`Q`])
///
/// Returns the owned Implementation code for the [`*trait*`]
/// trait with the signature:
///
/// ```impl *trait* for *type*```

macro_rules! arithmetic_trait_borrowed_to_owned {
    ($trait:ident, $trait_function:ident, $type:ident) => {
        impl $trait for $type {
            type Output = $type;

            fn $trait_function(self, other: Self) -> Self::Output {
                (&self).$trait_function(&other)
            }
        }
    };
}

pub(crate) use arithmetic_trait_borrowed_to_owned;

/// Implements the [`*trait*`] for owned [`*type*`] on borrowed [`*type*`] and
/// reverse using the [`*trait*`] for [`&*type*`].
///
/// Parameters:
/// - trait: the trait that is implemented (e.g. [`Add`], [`Sub`], ...).
/// - trait_function: the function the trait implements
/// (e.g. add for [`Add`], ...).
/// - type: the type the trait is implemented for (e.g. [`Z`], [`Q`], ...).
///
/// Returns the mixed owned and borrowed Implementation code for the
/// [`*trait*`] trait with the signatures:
///
/// ```impl *trait*<&*type*> for *type*```
///
/// ```impl *trait*<*type*> for &*type*```

macro_rules! arithmetic_trait_mixed_borrowed_owned {
    ($trait:ident, $trait_function:ident, $type:ident) => {
        impl $trait<$type> for &$type {
            type Output = $type;

            fn $trait_function(self, other: $type) -> Self::Output {
                self.$trait_function(&other)
            }
        }

        impl $trait<&$type> for $type {
            type Output = $type;

            fn $trait_function(self, other: &Self) -> Self::Output {
                (&self).$trait_function(other)
            }
        }
    };
}

pub(crate) use arithmetic_trait_mixed_borrowed_owned;
