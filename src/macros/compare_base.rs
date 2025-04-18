macro_rules! compare_base_get_mod {
    ($type:ident for $($source_type:ident)*) => {
        $(
        impl CompareBase<$source_type> for $type {
            paste::paste! {
                fn compare_base(&self, other: &$source_type) -> bool {
                    self.get_mod() == other.get_mod()
                }

                fn call_compare_base_error(&self, other: &$source_type) -> Option<MathError> {
                    Some(MathError::MismatchingModulus(format!(
                        "The moduli of the polynomial ring elements mismatch. One of them is {} and the other is {}.
                        The desired operation is not defined and an error is returned.",
                        self.get_mod(),
                        other.get_mod()
                    )))
                }
            }
        }
        impl CompareBase<&$source_type> for $type {
            paste::paste! {
                fn compare_base(&self, other: &&$source_type) -> bool {
                    self.get_mod() == other.get_mod()
                }

                fn call_compare_base_error(&self, other: &&$source_type) -> Option<MathError> {
                    Some(MathError::MismatchingModulus(format!(
                        "The moduli of the polynomial ring elements mismatch. One of them is {} and the other is {}.
                        The desired operation is not defined and an error is returned.",
                        self.get_mod(),
                        other.get_mod()
                    )))
                }
            }
        }
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

macro_rules! compare_base_get_mod_get_q {
    ($type:ident for $($source_type:ident)*) => {
        $(impl CompareBase<$source_type> for $type {
            paste::paste! {
                fn compare_base(&self, other: &$source_type) -> bool {
                    self.get_mod().get_q() == other.get_mod()
                }

                fn call_compare_base_error(&self, other: &$source_type) -> Option<MathError> {
                    Some(MathError::MismatchingModulus(format!(
                        "The moduli of the polynomial ring elements mismatch. One of them is {} and the other is {}.
                        The desired operation is not defined and an error is returned.",
                        self.get_mod(),
                        other.get_mod()
                    )))
                }
            }
        })*

        $(impl CompareBase<&$source_type> for $type {
            paste::paste! {
                fn compare_base(&self, other: &&$source_type) -> bool {
                    self.get_mod().get_q() == other.get_mod()
                }

                fn call_compare_base_error(&self, other: &&$source_type) -> Option<MathError> {
                    Some(MathError::MismatchingModulus(format!(
                        "The moduli of the polynomial ring elements mismatch. One of them is {} and the other is {}.
                        The desired operation is not defined and an error is returned.",
                        self.get_mod(),
                        other.get_mod()
                    )))
                }
            }
        })*
    };
}

pub(crate) use compare_base_default;
pub(crate) use compare_base_get_mod;
pub(crate) use compare_base_get_mod_get_q;
