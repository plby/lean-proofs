/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Dyadic spatial intervals and their logarithmic parametrization.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.UniformLogarithmicMean
import ErdosProblems.Erdos521.LogarithmicMoments

namespace Erdos521

open MeasureTheory Filter

noncomputable def dyadicPoint (k : ℕ) : ℝ := 1 - 1 / (2 : ℝ) ^ k

theorem dyadicPoint_lt_one (k : ℕ) : dyadicPoint k < 1 := sub_lt_self _ (by positivity)

theorem dyadicPoint_mono : Monotone dyadicPoint := by
  intro i j hij
  apply sub_le_sub_left
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij

theorem dyadicPoint_logGrid_zero (k : ℕ) :
    logGrid ((2 : ℝ) ^ (k + 1)) 2 (Real.log 2) 0 = dyadicPoint k := by
  rw [logGrid_zero, dyadicPoint, pow_succ]
  congr 1
  field_simp

theorem dyadicPoint_logGrid_one (k : ℕ) :
    logGrid ((2 : ℝ) ^ (k + 1)) 2 (Real.log 2) 1 = dyadicPoint (k + 1) := by
  have h := normalized_logGrid_one ((2 : ℝ) ^ (k + 1)) (Real.log 2)
  simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2), dyadicPoint] using h

theorem uniform_dyadic_interval_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ M : ℕ, 2 ≤ M ∧
      ∀ n k : ℕ, M ≤ n → (M : ℝ) ≤ (2 : ℝ) ^ (k + 1) →
        dyadicPoint (k + 1) ≤ endpointCenter C n →
        |(∫ ε, (intervalRootCount ε n (dyadicPoint k) (dyadicPoint (k + 1)) : ℝ) ∂sequenceLaw) -
          Real.log 2 / (2 * Real.pi)| < η := by
  obtain ⟨C, hC, hmean⟩ := uniform_logarithmic_mean
  refine ⟨C, hC, ?_⟩
  intro η hη
  obtain ⟨M, hM, hb⟩ := hmean (Real.log 2) (Real.log_pos (by norm_num)) η hη
  refine ⟨M, hM, ?_⟩
  intro n k hn hk hbulk
  have h := hb n hn ((2 : ℝ) ^ (k + 1)) hk hbulk
  have hleft : 1 - Real.exp (Real.log 2) / (2 : ℝ) ^ (k + 1) = dyadicPoint k := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact (logGrid_zero _ _ _).symm.trans (dyadicPoint_logGrid_zero k)
  simpa only [hleft, dyadicPoint] using h

theorem eventually_dyadic_interval_moments (p : ℕ) (hp : 1 ≤ p) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      9 / 10 ≤ dyadicPoint k →
      dyadicPoint (k + 1) ≤ endpointCenter (localMomentBulkConstant p) n →
      (∫ ε, (intervalRootCount ε n (dyadicPoint k) (dyadicPoint (k + 1)) : ℝ) ^ p ∂sequenceLaw) ≤ B := by
  obtain ⟨B, hB, hb⟩ := eventually_logarithmic_moments p hp (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨B, hB, ?_⟩
  filter_upwards [hb] with n hn
  intro k hl hu
  have h := hn ((2 : ℝ) ^ (k + 1)) 2 (by positivity) (by norm_num)
    (by simpa only [dyadicPoint_logGrid_zero] using hl)
    (by simpa only [dyadicPoint_logGrid_one] using hu)
  simpa only [dyadicPoint_logGrid_zero, dyadicPoint_logGrid_one] using h

end Erdos521
