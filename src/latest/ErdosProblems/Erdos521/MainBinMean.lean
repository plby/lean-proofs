/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The expected sum of central-bin root counts has the required logarithmic density.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.MainBinBulk
import ErdosProblems.Erdos521.TriangularMeans

namespace Erdos521

open MeasureTheory Filter
open scoped Topology BigOperators

theorem central_bin_sum_mean_limit :
    Tendsto (fun j : ℕ ↦ (∑ k ∈ mainBinSet j, ∫ ε,
      (intervalRootCount ε (2 ^ j) (dyadicPoint k) (dyadicPoint (k + 1)) : ℝ) ∂sequenceLaw) / j)
      atTop (𝓝 (Real.log 2 / (2 * Real.pi))) := by
  have hdegree : Tendsto (fun j : ℕ ↦ (2 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨C, _, hmean⟩ := uniform_dyadic_interval_mean
  have hlocal : ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j,
      |(∫ ε, (intervalRootCount ε (2 ^ j) (dyadicPoint k) (dyadicPoint (k + 1)) : ℝ) ∂sequenceLaw) -
        Real.log 2 / (2 * Real.pi)| < η := by
    intro η hη
    obtain ⟨M, _, hb⟩ := hmean η hη
    filter_upwards [hdegree.eventually_ge_atTop M, eventually_mainBin_scale (M : ℝ),
      eventually_mainBin_bulk C] with j hj hs hbulk
    intro k hk
    exact hb (2 ^ j) k hj (hs k hk) (hbulk k hk)
  simpa only [one_mul] using triangular_mean_limit mainBinSet
    (fun j k ↦ ∫ ε, (intervalRootCount ε (2 ^ j) (dyadicPoint k) (dyadicPoint (k + 1)) : ℝ) ∂sequenceLaw)
    1 (Real.log 2 / (2 * Real.pi)) (Eventually.of_forall mainBinSet_card_le) mainBinSet_card_ratio hlocal

theorem central_bin_endpoint_sum_limit :
    Tendsto (fun j : ℕ ↦ (∑ k ∈ mainBinSet j,
      sequenceLaw.real {ε | powerSum ε (2 ^ j + 1) (dyadicPoint k) = 0}) / (j : ℝ)) atTop (𝓝 0) := by
  have hdegree : Tendsto (fun j : ℕ ↦ (2 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlocal : ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j,
      |sequenceLaw.real {ε | powerSum ε (2 ^ j + 1) (dyadicPoint k) = 0} - 0| < η := by
    intro η hη
    obtain ⟨M, _, hb⟩ := uniform_polynomial_zero_probability η hη
    filter_upwards [hdegree.eventually_ge_atTop M, two_pow_sqrt_tendsto_atTop.eventually_ge_atTop (M : ℝ)]
      with j hj hM
    intro k hk
    have hs : (M : ℝ) ≤ (2 : ℝ) ^ k := hM.trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (mainBinSet_mem hk).1)
    simpa only [sub_zero, abs_of_nonneg measureReal_nonneg, dyadicPoint] using hb (2 ^ j) hj ((2 : ℝ) ^ k) hs
  simpa only [mul_zero] using triangular_mean_limit mainBinSet
    (fun j k ↦ sequenceLaw.real {ε | powerSum ε (2 ^ j + 1) (dyadicPoint k) = 0})
    1 0 (Eventually.of_forall mainBinSet_card_le) mainBinSet_card_ratio hlocal

end Erdos521
