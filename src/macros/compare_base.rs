macro_rules! compare_base_impl {
    ($type:ident, $source_type:ty, $get_mod_expr:expr) => {
        impl CompareBase<$source_type> for $type {
            paste::paste! {
                /// Compares the moduli of the two elements.
                ///
                /// Parameters:
                /// - `other`: The other object whose base is compared to `self`
                ///
                /// Returns true if the moduli match and false otherwise.
                fn compare_base(&self, other: &$source_type) -> bool {
                    $get_mod_expr(self) == other.get_mod()
                }

                /// Returns an error that gives a small explanation of how the moduli are
                /// incomparable.
                ///
                /// Parameters:
                /// - `other`: The other object whose base is compared to `self`
                ///
                /// Returns a MathError of type [`MismatchingModulus`](MathError::MismatchingModulus).
                fn call_compare_base_error(&self, other: &$source_type) -> Option<MathError> {
                    Some(MathError::MismatchingModulus(format!(
                        "The moduli of the elements mismatch. One of them is {} and the other is {}.
    The desired operation is not defined and an error is returned.",
                        $get_mod_expr(self),
                        other.get_mod()
                    )))
                }
            }
        }

        impl CompareBase<&$source_type> for $type {
            paste::paste! {
                /// Compares the moduli of the two elements.
                ///
                /// Parameters:
                /// - `other`: The other object whose base is compared to `self`
                ///
                /// Returns true if the moduli match and false otherwise.
                fn compare_base(&self, other: &&$source_type) -> bool {
                    $get_mod_expr(self) == other.get_mod()
                }

                /// Returns an error that gives a small explanation of how the moduli are
                /// incomparable.
                ///
                /// Parameters:
                /// - `other`: The other object whose base is compared to `self`
                ///
                /// Returns a MathError of type [`MismatchingModulus`](MathError::MismatchingModulus).
                fn call_compare_base_error(&self, other: &&$source_type) -> Option<MathError> {
                    Some(MathError::MismatchingModulus(format!(
                        "The moduli of the elements mismatch. One of them is {} and the other is {}.
    The desired operation is not defined and an error is returned.",
                        $get_mod_expr(self),
                        other.get_mod()
                    )))
                }
            }
        }
    };
}

macro_rules! compare_base_get_mod {
    ($type:ident for $($source_type:ident)*) => {
        $(
            compare_base_impl!($type, $source_type, |s: &$type| s.get_mod());
        )*
    };
}

macro_rules! compare_base_get_mod_get_q {
    ($type:ident for $($source_type:ident)*) => {
        $(
            compare_base_impl!($type, $source_type, |s: &$type| s.get_mod().get_q());
        )*
    };
}

macro_rules! compare_base_default {
    ($type:ident for $($source_type:ident)*) => {
        $(
            impl CompareBase<$source_type> for $type {}
            impl CompareBase<&$source_type> for $type {}
        )*
    };
}

pub(crate) use compare_base_default;
pub(crate) use compare_base_get_mod;
pub(crate) use compare_base_get_mod_get_q;
pub(crate) use compare_base_impl;
