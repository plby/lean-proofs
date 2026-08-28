import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite geometric approximations to the Cauchy kernel

The approximants are explicit finite polynomials in the pole variable.
Their exact remainders follow from the finite geometric-series identity.
All estimates below are uniform for a pole in a smaller closed disc and
a boundary point on the larger circle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximation

/-- The first `N` terms of the Cauchy kernel's geometric expansion. -/
def cauchyPartial (N : ℕ) (ξ z : ℂ) : ℂ :=
  ξ⁻¹ * ∑ i ∈ Finset.range N, (z / ξ) ^ i

/-- The finite geometric-series identity before division by `ξ - z`. -/
theorem sub_mul_cauchyPartial (N : ℕ) {ξ z : ℂ} (hξ : ξ ≠ 0) :
    (ξ - z) * cauchyPartial N ξ z = 1 - (z / ξ) ^ N := by
  have he : (ξ - z) * ξ⁻¹ = 1 - z / ξ := by
    rw [sub_mul, mul_inv_cancel₀ hξ, div_eq_mul_inv]
  calc
    _ = (∑ i ∈ Finset.range N, (z / ξ) ^ i) * ((ξ - z) * ξ⁻¹) := by
      unfold cauchyPartial
      ring
    _ = (∑ i ∈ Finset.range N, (z / ξ) ^ i) * (1 - z / ξ) := by rw [he]
    _ = _ := geom_sum_mul_neg (z / ξ) N

/-- The exact scalar Cauchy-kernel remainder, also valid when `N = 0`. -/
theorem cauchyPartial_error (N : ℕ) {ξ z : ℂ} (hξ : ξ ≠ 0) (hξz : ξ - z ≠ 0) :
    (ξ - z)⁻¹ - cauchyPartial N ξ z = (ξ - z)⁻¹ * (z / ξ) ^ N := by
  apply mul_left_cancel₀ hξz
  rw [mul_sub, mul_inv_cancel₀ hξz, sub_mul_cauchyPartial N hξ,
    ← mul_assoc, mul_inv_cancel₀ hξz, one_mul]
  ring

/-- Separation between the smaller disc and the boundary circle. -/
theorem cauchy_denominator_norm_lower_bound {r R : ℝ} {ξ z : ℂ}
    (hξ : ‖ξ‖ = R) (hz : ‖z‖ ≤ r) : R - r ≤ ‖ξ - z‖ := by
  have h := norm_sub_norm_le ξ z
  rw [hξ] at h
  linarith

theorem cauchy_denominator_ne_zero {r R : ℝ} {ξ z : ℂ}
    (hrR : r < R) (hξ : ‖ξ‖ = R) (hz : ‖z‖ ≤ r) : ξ - z ≠ 0 :=
  norm_pos_iff.mp ((sub_pos.mpr hrR).trans_le (cauchy_denominator_norm_lower_bound hξ hz))

/-- Uniform bound for the actual reciprocal Cauchy denominator. -/
theorem cauchyKernel_norm_le {r R : ℝ} {ξ z : ℂ}
    (hrR : r < R) (hξ : ‖ξ‖ = R) (hz : ‖z‖ ≤ r) :
    ‖(ξ - z)⁻¹‖ ≤ 1 / (R - r) := by
  simpa only [norm_inv, one_div] using
    one_div_le_one_div_of_le (sub_pos.mpr hrR) (cauchy_denominator_norm_lower_bound hξ hz)

/-- Uniform geometric decay of the exact finite-series remainder. -/
theorem cauchyPartial_error_norm_le (N : ℕ) {r R : ℝ} {ξ z : ℂ}
    (hr : 0 ≤ r) (hrR : r < R) (hξ : ‖ξ‖ = R) (hz : ‖z‖ ≤ r) :
    ‖(ξ - z)⁻¹ - cauchyPartial N ξ z‖ ≤ (r / R) ^ N / (R - r) := by
  have hR : 0 < R := hr.trans_lt hrR
  have hξ0 : ξ ≠ 0 := norm_pos_iff.mp (by simpa only [hξ] using hR)
  have hq : (‖z‖ / R) ^ N ≤ (r / R) ^ N :=
    pow_le_pow_left₀ (div_nonneg (norm_nonneg z) hR.le)
      (div_le_div_of_nonneg_right hz hR.le) N
  calc
    _ = ‖(ξ - z)⁻¹‖ * (‖z‖ / R) ^ N := by
      rw [cauchyPartial_error N hξ0 (cauchy_denominator_ne_zero hrR hξ hz),
        norm_mul, norm_pow, norm_div, hξ]
    _ ≤ (1 / (R - r)) * (r / R) ^ N :=
      mul_le_mul (cauchyKernel_norm_le hrR hξ hz) hq
        (pow_nonneg (div_nonneg (norm_nonneg z) hR.le) N) (by positivity)
    _ = _ := by ring

/-- The approximants are uniformly bounded independently of their degree. -/
theorem cauchyPartial_norm_le (N : ℕ) {r R : ℝ} {ξ z : ℂ}
    (hr : 0 ≤ r) (hrR : r < R) (hξ : ‖ξ‖ = R) (hz : ‖z‖ ≤ r) :
    ‖cauchyPartial N ξ z‖ ≤ 2 / (R - r) := by
  have hR : 0 < R := hr.trans_lt hrR
  have hq : (r / R) ^ N ≤ 1 :=
    pow_le_one₀ (div_nonneg hr hR.le) ((div_le_one hR).mpr hrR.le)
  have he : ‖(ξ - z)⁻¹ - cauchyPartial N ξ z‖ ≤ 1 / (R - r) :=
    (cauchyPartial_error_norm_le N hr hrR hξ hz).trans
      (div_le_div_of_nonneg_right hq (sub_nonneg.mpr hrR.le))
  calc
    ‖cauchyPartial N ξ z‖ = ‖(ξ - z)⁻¹ - ((ξ - z)⁻¹ - cauchyPartial N ξ z)‖ := by
      congr 1
      ring
    _ ≤ ‖(ξ - z)⁻¹‖ + ‖(ξ - z)⁻¹ - cauchyPartial N ξ z‖ := norm_sub_le _ _
    _ ≤ 1 / (R - r) + 1 / (R - r) := add_le_add (cauchyKernel_norm_le hrR hξ hz) he
    _ = _ := by ring

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscApproximation
