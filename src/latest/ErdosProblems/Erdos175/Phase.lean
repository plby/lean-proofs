/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# The standard additive phase and reciprocal-phase derivatives

This file packages the elementary complex identities for
`e(t) = exp(2 * pi * i * t)` and the real derivatives of `a / x` used in
reciprocal exponential sums.
-/

namespace Erdos175

noncomputable section

open Complex

/-- The standard additive character `e(t) = exp(2 * pi * i * t)`. -/
def e (t : ℝ) : ℂ :=
  Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * t)

@[simp]
lemma e_zero : e 0 = 1 := by
  simp [e]

/-- The additive character turns addition into multiplication. -/
lemma e_add (s t : ℝ) : e (s + t) = e s * e t := by
  rw [e, e, e, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Negating the argument inverts the additive character. -/
lemma e_neg (t : ℝ) : e (-t) = (e t)⁻¹ := by
  rw [e, e, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- The additive character never vanishes. -/
lemma e_ne_zero (t : ℝ) : e t ≠ 0 := by
  exact Complex.exp_ne_zero _

/-- The additive character takes values on the complex unit circle. -/
@[simp]
lemma norm_e (t : ℝ) : ‖e t‖ = 1 := by
  simp [e, Complex.norm_exp]

/-- Complex conjugation negates the argument of the additive character. -/
lemma conj_e (t : ℝ) : (starRingEnd ℂ) (e t) = e (-t) := by
  have harg :
      (starRingEnd ℂ) ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) =
        (2 * (Real.pi : ℂ) * Complex.I) * (-t : ℝ) := by
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_neg]
    ring
  rw [e, e, ← Complex.exp_conj, harg]

/-- A subtraction identity in the form used when expanding squared norms. -/
lemma e_sub (s t : ℝ) : e (s - t) = e s * (starRingEnd ℂ) (e t) := by
  rw [sub_eq_add_neg, e_add, conj_e]

/-- The quotient form of the subtraction identity. -/
lemma e_sub_eq_div (s t : ℝ) : e (s - t) = e s / e t := by
  rw [e_sub, div_eq_mul_inv, ← e_neg, conj_e]

/-- Integer arguments are periods of the standard additive character. -/
@[simp]
lemma e_int (n : ℤ) : e n = 1 := by
  rw [e]
  convert Complex.exp_int_mul_two_pi_mul_I n using 1
  push_cast
  ring_nf

/-- Translation by an integer does not change the additive character. -/
lemma e_add_int (t : ℝ) (n : ℤ) : e (t + n) = e t := by
  rw [e_add, e_int, mul_one]

/-- The real derivative of the standard additive character. -/
lemma hasDerivAt_e (t : ℝ) :
    HasDerivAt e ((2 * (Real.pi : ℂ) * Complex.I) * e t) t := by
  have hlin : HasDerivAt
      (fun z : ℂ ↦ (2 * (Real.pi : ℂ) * Complex.I) * z)
      (2 * (Real.pi : ℂ) * Complex.I) t :=
    hasDerivAt_const_mul _
  have h := (Complex.hasDerivAt_exp _).comp (t : ℂ) hlin
  change HasDerivAt
    (fun y : ℝ ↦ Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * y))
    ((2 * (Real.pi : ℂ) * Complex.I) *
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * t)) t
  apply h.comp_ofReal.congr_deriv
  ring

/-- The real reciprocal phase appearing in `e(a / x)`. -/
def reciprocalPhase (a x : ℝ) : ℝ := a / x

/-- First derivative of the real reciprocal phase. -/
lemma hasDerivAt_reciprocalPhase (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (reciprocalPhase a) (-a / x ^ 2) x := by
  have h := (hasDerivAt_inv hx).const_mul a
  have hd : a * (-(x ^ 2)⁻¹) = -a / x ^ 2 := by
    rw [div_eq_mul_inv]
    ring
  exact (h.congr_deriv hd).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Second derivative of `a / x`, expressed as a derivative of its first
derivative. -/
lemma hasDerivAt_reciprocalPhase_deriv (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ -a / y ^ 2) (2 * a / x ^ 3) x := by
  have h := (hasDerivAt_const (x := x) (-a)).div
    ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx)
  apply h.congr_deriv
  simp only [Pi.pow_apply, id_eq]
  field_simp [hx]
  ring

/-- Third derivative of `a / x`, expressed as a derivative of its second
derivative. -/
lemma hasDerivAt_reciprocalPhase_deriv2 (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ 2 * a / y ^ 3) (-6 * a / x ^ 4) x := by
  have h := (hasDerivAt_const (x := x) (2 * a)).div
    ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx)
  apply h.congr_deriv
  simp only [Pi.pow_apply, id_eq]
  field_simp [hx]
  ring

/-- Fourth derivative of `a / x`, expressed as a derivative of its third
derivative. -/
lemma hasDerivAt_reciprocalPhase_deriv3 (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ -6 * a / y ^ 4) (24 * a / x ^ 5) x := by
  have h := (hasDerivAt_const (x := x) (-6 * a)).div
    ((hasDerivAt_id x).pow 4) (pow_ne_zero 4 hx)
  apply h.congr_deriv
  simp only [Pi.pow_apply, id_eq]
  field_simp [hx]
  ring

/-- Derivative of the complex reciprocal exponential phase `e(a / x)`. -/
lemma hasDerivAt_e_reciprocal (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ e (reciprocalPhase a y))
      ((-a / x ^ 2 : ℝ) * ((2 * (Real.pi : ℂ) * Complex.I) *
        e (reciprocalPhase a x))) x := by
  have h := (hasDerivAt_e (reciprocalPhase a x)).scomp (𝕜 := ℝ) x
    (hasDerivAt_reciprocalPhase a hx)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)

end

end Erdos175
