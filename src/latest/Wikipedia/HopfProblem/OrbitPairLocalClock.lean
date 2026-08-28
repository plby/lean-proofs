import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# A bounded clock with a prescribed unit derivative

Inside any open time interval around a chosen time, a compactly supported
smooth clock vanishes at that time and has derivative one there. Its
absolute value is at most one, so it drives all sufficiently small ambient
bump parameters uniformly in time.
-/

noncomputable section

open Set Function Filter Metric
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.OrbitPair.ClockVelocity

theorem exists_local_clock {U : Set ℝ} (hU : IsOpen U) {t₀ : ℝ} (ht₀ : t₀ ∈ U) :
    ∃ κ : ℝ → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
      (∀ t, ‖κ t‖ ≤ 1) ∧ κ t₀ = 0 ∧ deriv κ t₀ = 1 ∧
      (∀ t ∉ U, κ t = 0) := by
  obtain ⟨β, hsupport, hcompact, hβ, hrange, hone⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
      (inter_mem (hU.mem_nhds ht₀) (ball_mem_nhds t₀ (by norm_num : (0 : ℝ) < 1)))
  let κ : ℝ → ℝ := fun t => β t * (t - t₀)
  have hκ : ContDiff ℝ ∞ κ := hβ.mul (contDiff_id.sub contDiff_const)
  refine ⟨κ, hκ, hcompact.mul_right, ?_, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : β t = 0
    · simp only [κ, ht, zero_mul, norm_zero, zero_le_one]
    · have htball : t ∈ ball t₀ 1 := (hsupport (subset_tsupport β ht)).2
      have hdist : ‖t - t₀‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using htball
      have hβnorm : ‖β t‖ ≤ 1 := by
        have hb := hrange (mem_range_self t)
        simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
      calc
        ‖κ t‖ = ‖β t‖ * ‖t - t₀‖ := norm_mul _ _
        _ ≤ 1 * ‖t - t₀‖ := mul_le_mul_of_nonneg_right hβnorm (norm_nonneg _)
        _ ≤ 1 := by simpa only [one_mul] using hdist.le
  · simp only [κ, sub_self, mul_zero]
  · have hd := ((hβ.differentiable (by simp) t₀).hasDerivAt).mul
      ((hasDerivAt_id t₀).sub_const t₀)
    have hdκ : HasDerivAt κ 1 t₀ := by
      convert! hd using 1 <;>
        simp only [id_eq, sub_self, mul_zero, zero_add, hone, mul_one]
    exact hdκ.deriv
  · intro t ht
    have hz : β t = 0 := by
      by_contra hn
      exact ht (hsupport (subset_tsupport β hn)).1
    simp only [κ, hz, zero_mul]

end Wikipedia.HopfProblem.OrbitPair.ClockVelocity
