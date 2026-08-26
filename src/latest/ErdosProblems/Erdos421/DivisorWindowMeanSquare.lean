import ErdosProblems.Erdos421.WeightedDivisorWindows
import ErdosProblems.Erdos421.DivisorWindowContinuity

/-! # A mean-square estimate for the full normalized divisibility window -/

namespace Erdos421

open MeasureTheory FourierTransform
open scoped SchwartzMap

/-- The full Poisson series, including its uniformly bounded tail, satisfies
the type-I mean-square estimate. No short-interval prime estimate is assumed. -/
theorem weighted_divisor_window_mean_square (φ : 𝓢(ℝ, ℂ)) {C₁ C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (hφ₁ : ∀ t : ℝ, ‖𝓕 φ t‖ ≤ C₁ / (1 + |t|))
    (hφ₂ : ∀ t : ℝ, |t| ^ 2 * ‖𝓕 φ t‖ ≤ C₂)
    (S : Finset ℕ) (a : ℕ → ℂ) {M H : ℕ} (hM : 0 < M) (hH : 0 < H)
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M) (ha : ∀ m ∈ S, ‖a m‖ ≤ 1)
    {Y : ℝ} (hY : 0 < Y) {u v : ℝ} (huv : u ≤ v) :
    (∫ x in u..v, ‖∑ m ∈ S, a m * (additiveDivisorWindow φ Y x m -
      (m : ℂ)⁻¹ * (∫ z : ℝ, φ z))‖ ^ 2) ≤
      2 * ((v - u + 16 * M ^ 2 * Real.log (4 * Real.pi * H * M ^ 2 + 2)) *
        (2 * C₁ ^ 2 * (harmonic M : ℝ) ^ 3 / Y)) +
      2 * (v - u) * (2 * C₂ * M ^ 2 / (Y ^ 2 * H)) ^ 2 := by
  let R : ℝ → ℂ := fun x ↦ ∑ m ∈ S, a m * (additiveDivisorWindow φ Y x m -
    (m : ℂ)⁻¹ * (∫ z : ℝ, φ z))
  let P : ℝ → ℂ := fun x ↦ ∑ m ∈ S, a m * divisorWindowFinitePart φ Y H x m
  let E : ℝ := 2 * C₂ * M ^ 2 / (Y ^ 2 * H)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hR : Continuous R := by
    apply continuous_finsetSum
    intro m hm
    exact continuous_const.mul ((additiveDivisorWindow_continuous φ hY (hS m hm).1).sub
      continuous_const)
  have hP : Continuous P := by
    apply continuous_finsetSum
    intro m hm
    exact continuous_const.mul (divisorWindowFinitePart_continuous φ Y H m)
  have herror (x : ℝ) : ‖R x - P x‖ ≤ E :=
    weighted_divisor_window_truncation_error φ hC₂ hφ₂ S a hS ha hY hH x
  have hpoint (x : ℝ) : ‖R x‖ ^ 2 ≤ 2 * ‖P x‖ ^ 2 + 2 * E ^ 2 := by
    have hb : ‖R x‖ ≤ ‖P x‖ + E := by
      calc
        _ = ‖(R x - P x) + P x‖ := by rw [sub_add_cancel]
        _ ≤ ‖R x - P x‖ + ‖P x‖ := norm_add_le _ _
        _ ≤ E + ‖P x‖ := add_le_add (herror x) le_rfl
        _ = _ := add_comm _ _
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    nlinarith [sq_nonneg (‖P x‖ - E)]
  have hPint : IntervalIntegrable (fun x ↦ 2 * ‖P x‖ ^ 2) volume u v :=
    (continuous_const.mul (hP.norm.pow 2)).intervalIntegrable u v
  have hEint : IntervalIntegrable (fun _ : ℝ ↦ 2 * E ^ 2) volume u v := intervalIntegrable_const
  have hi := intervalIntegral.integral_mono_on huv
    ((hR.norm.pow 2).intervalIntegrable u v) (hPint.add hEint) (fun x _ ↦ hpoint x)
  rw [intervalIntegral.integral_add hPint hEint, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul, Pi.pow_apply] at hi
  have hm := weighted_divisor_finite_part_mean φ hφ₁ S a hM hS ha hY huv (H := H)
  change (∫ x in u..v, ‖P x‖ ^ 2) ≤ _ at hm
  change (∫ x in u..v, ‖R x‖ ^ 2) ≤ _
  dsimp only [E] at hi
  nlinarith

end Erdos421
