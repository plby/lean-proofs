/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The expected distinct root count on the central dyadic interval.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.MainBinMean
import ErdosProblems.Erdos521.IcoPartitionExpectation

namespace Erdos521

open MeasureTheory Filter
open scoped Topology BigOperators

theorem central_interval_mean_div_index_limit :
    Tendsto (fun j : ℕ ↦ (∫ ε,
      (intervalRootCount ε (2 ^ j) (dyadicPoint (Nat.sqrt j)) (dyadicPoint (j - Nat.sqrt j)) : ℝ)
        ∂sequenceLaw) / j) atTop (𝓝 (Real.log 2 / (2 * Real.pi))) := by
  have hstart : Tendsto (fun j : ℕ ↦ sequenceLaw.real
      {ε | powerSum ε (2 ^ j + 1) (dyadicPoint (Nat.sqrt j)) = 0} / (j : ℝ)) atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero (b := 0) (B := 1)
    · exact Eventually.of_forall (fun _ ↦ measureReal_nonneg)
    · exact Eventually.of_forall (fun _ ↦ measureReal_le_one)
    · exact tendsto_natCast_atTop_atTop
  have h := (central_bin_sum_mean_limit.add hstart).sub central_bin_endpoint_sum_limit
  simp only [add_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 4] with j hj
  have hab : Nat.sqrt j ≤ j - Nat.sqrt j := by have := two_sqrt_le hj; omega
  have hid := integral_intervalRootCount_Ico_identity (2 ^ j) (Nat.sqrt j) (j - Nat.sqrt j)
    hab dyadicPoint dyadicPoint_mono
  change _ / (j : ℝ) + _ / (j : ℝ) - _ / (j : ℝ) = _ / (j : ℝ)
  rw [← add_div, ← sub_div]
  congr 1
  dsimp only [mainBinSet]
  linarith

theorem central_interval_mean_div_log_limit :
    Tendsto (fun j : ℕ ↦ (∫ ε,
      (intervalRootCount ε (2 ^ j) (dyadicPoint (Nat.sqrt j)) (dyadicPoint (j - Nat.sqrt j)) : ℝ)
        ∂sequenceLaw) / Real.log ((2 ^ j : ℕ) : ℝ)) atTop (𝓝 (1 / (2 * Real.pi))) := by
  have h := central_interval_mean_div_index_limit.div_const (Real.log 2)
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have heq : (Real.log 2 / (2 * Real.pi)) / Real.log 2 = 1 / (2 * Real.pi) := by field_simp
  rw [heq] at h
  convert h using 1
  funext j
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, div_div]

end Erdos521
