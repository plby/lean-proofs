/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An elementary integral square bound used for local root probabilities.
Formal proof: Codex.
-/
import Mathlib

namespace Erdos521

open MeasureTheory

theorem interval_integral_sq_le (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, (f t) ^ 2 := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let L := b - a
  let I := ∫ t in a..b, f t
  let J := ∫ t in a..b, (f t) ^ 2
  have hL : 0 < L := sub_pos.mpr hab
  have hfint := hf.intervalIntegrable (μ := volume) a b
  have hsqint : IntervalIntegrable (fun t ↦ (f t) ^ 2) volume a b :=
    (hf.pow 2).intervalIntegrable a b
  have h₁ : IntervalIntegrable (fun t ↦ L ^ 2 * (f t) ^ 2) volume a b := hsqint.const_mul _
  have h₂ : IntervalIntegrable (fun t ↦ (2 * L * I) * f t) volume a b := hfint.const_mul _
  have h₃ : IntervalIntegrable (fun _ : ℝ ↦ I ^ 2) volume a b := intervalIntegrable_const
  have hid : (∫ t in a..b, (L * f t - I) ^ 2) = L ^ 2 * J - L * I ^ 2 := by
    calc
      (∫ t in a..b, (L * f t - I) ^ 2) =
          ∫ t in a..b, (L ^ 2 * (f t) ^ 2 - (2 * L * I) * f t + I ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = L ^ 2 * J - L * I ^ 2 := by
        rw [intervalIntegral.integral_add (h₁.sub h₂) h₃,
          intervalIntegral.integral_sub h₁ h₂, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        change L ^ 2 * J - (2 * L * I) * I + L * I ^ 2 = _
        ring
  have hnonneg := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab.le
    (fun t : ℝ ↦ sq_nonneg (L * f t - I))
  rw [hid] at hnonneg
  have hmul : 0 ≤ L * (L * J - I ^ 2) := by nlinarith
  have h := (mul_nonneg_iff_of_pos_left hL).mp hmul
  change I ^ 2 ≤ L * J
  linarith

end Erdos521
