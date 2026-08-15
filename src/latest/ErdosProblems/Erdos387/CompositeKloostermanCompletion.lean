/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.KloostermanOrthogonality
import Waring.Analytic.FourierCoefficientSum

/-!
# Fourier completion for incomplete composite-modulus Kloosterman sums

This is the exact completion step surrounding BNPZ Lemma 8.2.  It is valid
for every nonzero modulus.  The still-deep input in Lemma 8.2 is the
pointwise bound for the completed sums; this file isolates that input without
assuming it.
-/

namespace Erdos387

open scoped BigOperators

namespace Kloosterman

/-- The inverse phase, extended by zero away from the units, summed on the
integer interval M < x ≤ M+m. -/
noncomputable def incompleteInterval
    (q : ℕ) [NeZero q] (b : ZMod q) (M : ℤ) (m : ℕ) : ℂ :=
  ∑ x ∈ Finset.Ioc M (M + m), coefficient q b (x : ZMod q)

/-- Exact finite Fourier completion of an incomplete Kloosterman sum. -/
theorem incompleteInterval_eq_complete
    (q : ℕ) [NeZero q] (b : ZMod q) (M : ℤ) (m : ℕ) :
    incompleteInterval q b M m =
      (q : ℂ)⁻¹ * ∑ a : ZMod q,
        Waring.Analytic.intervalFourierCoefficient M m a * sum q a b := by
  unfold incompleteInterval Waring.Analytic.intervalFourierCoefficient
  symm
  calc
    (q : ℂ)⁻¹ * ∑ a : ZMod q,
        (∑ x ∈ Finset.Ioc M (M + m),
          ZMod.stdAddChar (-(a * (x : ZMod q)))) * sum q a b =
      (q : ℂ)⁻¹ * ∑ a : ZMod q,
        ∑ x ∈ Finset.Ioc M (M + m),
          ZMod.stdAddChar (-(a * (x : ZMod q))) * sum q a b := by
      simp_rw [Finset.sum_mul]
    _ = (q : ℂ)⁻¹ * ∑ x ∈ Finset.Ioc M (M + m),
        ∑ a : ZMod q,
          ZMod.stdAddChar (-(a * (x : ZMod q))) * sum q a b := by
      congr 1
      rw [Finset.sum_comm]
    _ = (q : ℂ)⁻¹ * ∑ x ∈ Finset.Ioc M (M + m),
        (q : ℂ) * coefficient q b (x : ZMod q) := by
      apply congrArg ((q : ℂ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro x _hx
      exact AdditiveOrthogonality.sum_stdAddChar_neg_mul_fourierSum
        (coefficient q b) (x : ZMod q)
    _ = ∑ x ∈ Finset.Ioc M (M + m),
        coefficient q b (x : ZMod q) := by
      rw [← Finset.mul_sum]
      have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
      rw [← mul_assoc, inv_mul_cancel₀ hq, one_mul]

/-- A uniform pointwise bound for the completed Kloosterman sums yields the
standard logarithmic-loss bound for every interval of length at most the
modulus. -/
theorem norm_incompleteInterval_le_log_of_complete_bound
    (q : ℕ) [NeZero q] (b : ZMod q) (M : ℤ) (m : ℕ)
    (B : ℝ) (hm : m ≤ q) (hB : 0 ≤ B)
    (hcomplete : ∀ a : ZMod q, ‖sum q a b‖ ≤ B) :
    ‖incompleteInterval q b M m‖ ≤ (Real.log q + 1) * B := by
  rw [incompleteInterval_eq_complete]
  have hqReal : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  calc
    ‖(q : ℂ)⁻¹ * ∑ a : ZMod q,
        Waring.Analytic.intervalFourierCoefficient M m a * sum q a b‖ =
      (q : ℝ)⁻¹ * ‖∑ a : ZMod q,
        Waring.Analytic.intervalFourierCoefficient M m a * sum q a b‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (q : ℝ)⁻¹ * ∑ a : ZMod q,
        ‖Waring.Analytic.intervalFourierCoefficient M m a * sum q a b‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (q : ℝ)⁻¹ * ∑ a : ZMod q,
        ‖Waring.Analytic.intervalFourierCoefficient M m a‖ *
          ‖sum q a b‖ := by
      simp only [norm_mul]
    _ ≤ (q : ℝ)⁻¹ * ∑ a : ZMod q,
        ‖Waring.Analytic.intervalFourierCoefficient M m a‖ * B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hcomplete a) (norm_nonneg _)
    _ = (q : ℝ)⁻¹ *
        (∑ a : ZMod q,
          ‖Waring.Analytic.intervalFourierCoefficient M m a‖) * B := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ (q : ℝ)⁻¹ * ((q : ℝ) * (Real.log q + 1)) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact mul_le_mul_of_nonneg_left
        (Waring.Analytic.sum_norm_intervalFourierCoefficient_le q M m hm)
        (by positivity)
    _ = (Real.log q + 1) * B := by
      field_simp

end Kloosterman

end Erdos387
