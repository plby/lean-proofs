import ErdosProblems.Erdos633b.CosinePolynomialLifts

/-! Cubic and quartic independence at primitive rational-angle cosines.
The proof uses exact cyclotomic degree, not a numerical root calculation. -/

namespace Erdos633b
open Polynomial

theorem primitive_cosine_root (M k : ℕ) (hM : 0 < M) (hk : k.Coprime M) :
    IsPrimitiveRoot
      (Complex.exp (((2 * Real.pi * k / M : ℝ) : ℂ) * Complex.I)) M := by
  convert Complex.isPrimitiveRoot_exp_of_coprime k M hM.ne' hk using 1
  congr 1
  push_cast
  ring

theorem exp_add_inv_eq_two_cos (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) + (Complex.exp ((x : ℂ) * Complex.I))⁻¹ =
      ((2 * Real.cos x : ℝ) : ℂ) := by
  rw [← Complex.exp_neg]
  have hn : -((x : ℂ) * Complex.I) = (-x : ℂ) * Complex.I := by ring
  rw [hn, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

theorem quartic_cosine_independent (M k : ℕ) (hM : 0 < M) (hk : k.Coprime M)
    (hdeg : 8 < M.totient) (a : Fin 5 → ℚ)
    (he : (a 0 : ℝ) + a 1 * (2 * Real.cos (2 * Real.pi * k / M)) +
      a 2 * (2 * Real.cos (2 * Real.pi * k / M)) ^ 2 +
      a 3 * (2 * Real.cos (2 * Real.pi * k / M)) ^ 3 +
      a 4 * (2 * Real.cos (2 * Real.pi * k / M)) ^ 4 = 0) : ∀ i, a i = 0 := by
  let x : ℝ := 2 * Real.pi * k / M
  let z := Complex.exp ((x : ℂ) * Complex.I)
  have hz : IsPrimitiveRoot z M := primitive_cosine_root M k hM hk
  have he' : (a 0 : ℂ) + a 1 * ((2 * Real.cos x : ℝ) : ℂ) +
      a 2 * ((2 * Real.cos x : ℝ) : ℂ) ^ 2 +
      a 3 * ((2 * Real.cos x : ℝ) : ℂ) ^ 3 +
      a 4 * ((2 * Real.cos x : ℝ) : ℂ) ^ 4 = 0 := by exact_mod_cast he
  have hzero : aeval z (quarticCosineLift a) = 0 := by
    rw [quarticCosineLift_eval a z (Complex.exp_ne_zero _), exp_add_inv_eq_two_cos x, he',
      mul_zero]
  exact quarticCosineLift_coeffs_zero a
    (zero_of_primitive_root_and_small_degree M hM z hz _ hzero
      (lt_of_le_of_lt (quarticCosineLift_degree a) hdeg))

theorem cubic_cosine_independent (M k : ℕ) (hM : 0 < M) (hk : k.Coprime M)
    (hdeg : 6 < M.totient) (a : Fin 4 → ℚ)
    (he : (a 0 : ℝ) + a 1 * (2 * Real.cos (2 * Real.pi * k / M)) +
      a 2 * (2 * Real.cos (2 * Real.pi * k / M)) ^ 2 +
      a 3 * (2 * Real.cos (2 * Real.pi * k / M)) ^ 3 = 0) : ∀ i, a i = 0 := by
  let x : ℝ := 2 * Real.pi * k / M
  let z := Complex.exp ((x : ℂ) * Complex.I)
  have hz : IsPrimitiveRoot z M := primitive_cosine_root M k hM hk
  have he' : (a 0 : ℂ) + a 1 * ((2 * Real.cos x : ℝ) : ℂ) +
      a 2 * ((2 * Real.cos x : ℝ) : ℂ) ^ 2 +
      a 3 * ((2 * Real.cos x : ℝ) : ℂ) ^ 3 = 0 := by exact_mod_cast he
  have hzero : aeval z (cubicCosineLift a) = 0 := by
    rw [cubicCosineLift_eval a z (Complex.exp_ne_zero _), exp_add_inv_eq_two_cos x, he',
      mul_zero]
  exact cubicCosineLift_coeffs_zero a
    (zero_of_primitive_root_and_small_degree M hM z hz _ hzero
      (lt_of_le_of_lt (cubicCosineLift_degree a) hdeg))

end Erdos633b
