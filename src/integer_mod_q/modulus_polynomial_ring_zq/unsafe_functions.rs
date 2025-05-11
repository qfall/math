// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.

use super::ModulusPolynomialRingZq;
use crate::macros::unsafe_passthrough::unsafe_getter_mod;
use flint_sys::fq::{fq_ctx_clear, fq_ctx_struct};

unsafe_getter_mod!(ModulusPolynomialRingZq, modulus, fq_ctx_struct);

impl ModulusPolynomialRingZq {
    /// Sets a mutable reference to the field `modulus` of type [`ModulusPolynomialRingZq`] to a given `fq_ctx_struct`.
    ///
    /// Parameters:
    /// - `flint_struct`: value to set the attribute to
    ///
    /// **WARNING:** The returned struct is part of [`flint_sys`].
    /// Any changes to this object are unsafe and may introduce memory leaks.
    /// Please be aware that most moduli are shared across multiple instances and all
    /// modifications of this struct will affect any other instance with a reference to this object.
    ///
    /// This function is a passthrough to enable users of this library to use [`flint_sys`]
    /// and with that [FLINT](https://flintlib.org/) functions that might not be covered in our library yet.
    /// If this is the case, please consider contributing to this open-source project
    /// by opening a Pull Request at [qfall_math](https://github.com/qfall/math)
    /// to provide this feature in the future.
    ///
    /// # Safety
    /// Ensure that the old `modulus` does not share any memory with any moduli
    /// that might be used in the future. The memory of the old `modulus` is freed
    /// using this function.
    ///
    /// Any [`flint_sys`] struct and function is part of a FFI to the C-library `FLINT`.
    /// As `FLINT` is a C-library, it does not provide all memory safety features
    /// that Rust and our Wrapper provide.
    /// Thus, using functions of [`flint_sys`] can introduce memory leaks.
    pub unsafe fn set_fq_ctx_struct(&mut self, flint_struct: fq_ctx_struct) {
        let modulus = std::rc::Rc::<fq_ctx_struct>::get_mut(&mut self.modulus).unwrap();

        // free memory of old modulus before new values of modulus are copied
        unsafe { fq_ctx_clear(modulus) };

        modulus.a = flint_struct.a;
        modulus.ctxp = flint_struct.ctxp;
        modulus.inv = flint_struct.inv;
        modulus.is_conway = flint_struct.is_conway;
        modulus.j = flint_struct.j;
        modulus.len = flint_struct.len;
        modulus.modulus = flint_struct.modulus;
        modulus.sparse_modulus = flint_struct.sparse_modulus;
        modulus.var = flint_struct.var;
    }
}

#[cfg(test)]
mod test_get_fq_ctx_struct {
    use super::ModulusPolynomialRingZq;
    use crate::integer_mod_q::Zq;

    /// Checks availability of the getter for [`ModulusPolynomialRingZq::modulus`]
    /// and its ability to be modified.
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let zq = Zq::from((3, 7));
        let mut modulus = ModulusPolynomialRingZq::from(zq);
        let cmp_zq = Zq::from((3, 5));
        let cmp_mod = ModulusPolynomialRingZq::from(cmp_zq);

        let mut fmpz_mod = unsafe { modulus.get_fq_ctx_struct() };

        fmpz_mod.ctxp[0].n[0].0 = 5;

        assert_eq!(cmp_mod, modulus);
    }
}

#[cfg(test)]
mod test_set_fq_ctx_struct {
    use super::ModulusPolynomialRingZq;
    use crate::{integer::Z, integer_mod_q::Zq, traits::GetCoefficient};
    use flint_sys::{
        fmpz::fmpz,
        fmpz_mod::fmpz_mod_ctx_init,
        fmpz_mod_poly::{fmpz_mod_poly_init, fmpz_mod_poly_set_coeff_fmpz},
        fq::fq_ctx_init_modulus,
    };
    use std::{ffi::CString, mem::MaybeUninit};

    /// Checks availability of the setter for [`ModulusPolynomialRingZq::modulus`]
    /// and its ability to modify [`ModulusPolynomialRingZq`].
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let zq = Zq::from((3, 7));
        let mut test_struct = ModulusPolynomialRingZq::from(zq);
        // Setup modulus, i.e. mod 11
        let mut modulus = MaybeUninit::uninit();
        let mut modulus = unsafe {
            fmpz_mod_ctx_init(modulus.as_mut_ptr(), &fmpz(11));
            modulus.assume_init()
        };
        // Setup ModulusPolynomial, i.e. 7 mod 11
        let mut poly = MaybeUninit::uninit();
        let mut poly = unsafe {
            fmpz_mod_poly_init(poly.as_mut_ptr(), &modulus);
            poly.assume_init()
        };
        unsafe {
            fmpz_mod_poly_set_coeff_fmpz(&mut poly, 0, &fmpz(7), &modulus);
        };
        // Setup ModPolynomialRingZq
        let mut mod_poly_ring_zq = MaybeUninit::uninit();
        let c_string = CString::new("X").unwrap();
        let mod_poly_ring_zq = unsafe {
            fq_ctx_init_modulus(
                mod_poly_ring_zq.as_mut_ptr(),
                &poly,
                &modulus,
                c_string.as_ptr(),
            );
            mod_poly_ring_zq.assume_init()
        };

        unsafe { test_struct.set_fq_ctx_struct(mod_poly_ring_zq) };

        assert_eq!(Z::from(11), test_struct.get_q());
        assert_eq!(0, test_struct.get_degree());
        assert_eq!(
            Z::from(7),
            GetCoefficient::<Z>::get_coeff(&test_struct, 0).unwrap()
        );
    }
}
