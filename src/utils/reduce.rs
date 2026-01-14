use std::cmp::min;

use flint_sys::{
    fmpz::{fmpz_submul, fmpz_zero},
    fmpz_mod::{fmpz_mod_ctx_struct, fmpz_mod_set_fmpz},
    fmpz_mod_poly::fmpz_mod_poly_struct,
    fmpz_poly::fmpz_poly_struct,
};

pub(crate) unsafe fn internal_reduce(
    poly: &mut fmpz_poly_struct,
    nr_coeffs_poly: usize,
    modulus_polynomial: &fmpz_mod_poly_struct,
    nr_coeffs_modulus_poly: usize,
    modulus: &fmpz_mod_ctx_struct,
) {
    let (poly_len, modulus_polynomial_len) = (nr_coeffs_poly, nr_coeffs_modulus_poly);

    // X**3 + X**2 + 58X + 2 / X**3 + 1

    // X**a + ... / X**b + ...
    if poly_len >= modulus_polynomial_len {
        // for i in (b..=a)
        for i in (modulus_polynomial_len..=poly_len).rev() {
            // for i in 0..b
            for k in 0..modulus_polynomial_len {
                unsafe {
                    fmpz_submul(
                        (poly.coeffs).add((i - modulus_polynomial_len) + k),
                        poly.coeffs.add(i),
                        modulus_polynomial.coeffs.add(k),
                    )
                };
            }
            unsafe { fmpz_zero(poly.coeffs.add(i)) };
        }
    }

    for i in 0..=min(poly_len, modulus_polynomial_len - 1) {
        unsafe { fmpz_mod_set_fmpz(poly.coeffs.add(i), poly.coeffs.add(i), modulus) };
    }
}
