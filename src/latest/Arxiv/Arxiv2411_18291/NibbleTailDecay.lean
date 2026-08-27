import Arxiv.Arxiv2411_18291.AsymptoticTypicality

/-! # A polynomial number of nibble tests is dominated by a positive-power exponential -/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem eventually_nibble_tail_lt_one (r : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      5 * (n : ℝ) ^ (2 * (r + 1)) * Real.exp (-((n : ℝ) ^ η)) < 1 := by
  have ht := (typicality_exp_bound_tendsto (2 * (r + 1)) 1 hη).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [ht] with n hn
  norm_num only [Nat.mul_one] at hn
  have hpow : 0 ≤ (n : ℝ) ^ η := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hexp : Real.exp (-((n : ℝ) ^ η)) ≤ Real.exp (-((n : ℝ) ^ η / 12)) :=
    Real.exp_le_exp.mpr (by linarith only [hpow])
  have hcoef : 5 * (n : ℝ) ^ (2 * (r + 1)) ≤ 6 * (n : ℝ) ^ (2 * (r + 1)) := by
    have h := pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (2 * (r + 1))
    linarith only [h]
  exact (mul_le_mul hcoef hexp (Real.exp_pos _).le (by positivity)).trans_lt hn

end Arxiv2411_18291
