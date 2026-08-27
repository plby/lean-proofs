/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CenteredStepBounds
import ErdosProblems.Erdos207.ConfigurationVariancePower

/-! # Common power bounds after centering a raw greedy observable -/

namespace Erdos207

theorem centered_step_abs_power
    (N t sigma x df de : ℝ) (z r d : ℕ) (hN : 1 ≤ N) (ht : 2 ≤ t) (hsigma : |sigma| = 1)
    (hx : |x| ≤ N ^ z * t ^ r) (hdet : |df| + |de| ≤ N ^ z / N * t ^ d) :
    |sigma * (x - df) - de| ≤ N ^ z * t ^ (max r d + 1) := by
  have hNpos : 0 < N := by linarith
  have htpos : 0 < t := by linarith
  have hdiv : N ^ z / N ≤ N ^ z := div_le_self (pow_nonneg hNpos.le _) hN
  have hd := hdet.trans (mul_le_mul_of_nonneg_right hdiv (pow_nonneg htpos.le _))
  have hrpow : t ^ r ≤ t ^ max r d := pow_le_pow_right₀ (by linarith) (le_max_left _ _)
  have hdpow : t ^ d ≤ t ^ max r d := pow_le_pow_right₀ (by linarith) (le_max_right _ _)
  have hpoly : t ^ r + t ^ d ≤ t ^ (max r d + 1) := by
    calc
      _ ≤ 2 * t ^ max r d := by linarith
      _ ≤ t * t ^ max r d := mul_le_mul_of_nonneg_right ht (by positivity)
      _ = _ := by rw [pow_succ]; ring
  calc
    _ ≤ |x| + |df| + |de| := centered_step_abs_le sigma x df de hsigma
    _ ≤ N ^ z * (t ^ r + t ^ d) := by linarith only [hx, hd]
    _ ≤ _ := mul_le_mul_of_nonneg_left hpoly (pow_nonneg hNpos.le _)

theorem centered_step_secondMoment_power
    {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω) (X : Ω → ℝ)
    (N t sigma df de : ℝ) (z r d : ℕ) (hN : 1 ≤ N) (ht : 2 ≤ t) (hsigma : |sigma| = 1)
    (hraw : L.expectationReal (fun ω ↦ X ω ^ 2) ≤ N ^ (2 * z) / N * t ^ r)
    (hdet : |df| + |de| ≤ N ^ z / N * t ^ d) :
    L.expectationReal (fun ω ↦ (sigma * (X ω - df) - de) ^ 2) ≤
      N ^ (2 * z) / N * t ^ (max r (2 * d) + 2) := by
  have hcenter := centered_step_secondMoment_le L X sigma df de
    (N ^ (2 * z) / N * t ^ r) hsigma hraw
  exact hcenter.trans (centered_second_moment_power N t (N ^ (2 * z) / N * t ^ r)
    (|df| + |de|) z r d hN ht (by positivity) le_rfl hdet)

end Erdos207
