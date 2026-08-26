/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
All central dyadic bins eventually satisfy every fixed bulk constraint.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.MainBins
import ErdosProblems.Erdos521.DyadicIntervals

namespace Erdos521

open Filter
open scoped Topology

theorem two_pow_sqrt_tendsto_atTop : Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ Nat.sqrt j) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp nat_sqrt_tendsto_atTop

theorem eventually_mainBin_scale (M : ℝ) :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j, M ≤ (2 : ℝ) ^ (k + 1) := by
  filter_upwards [two_pow_sqrt_tendsto_atTop.eventually_ge_atTop M] with j hj
  intro k hk
  exact hj.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by
    have := (mainBinSet_mem hk).1
    omega))

theorem eventually_mainBin_lower :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j, 9 / 10 ≤ dyadicPoint k := by
  have hlim : Tendsto (fun j : ℕ ↦ dyadicPoint (Nat.sqrt j)) atTop (𝓝 1) :=
    inverse_scale_point_tendsto _ two_pow_sqrt_tendsto_atTop 1
  filter_upwards [hlim.eventually (lt_mem_nhds (by norm_num : (9 / 10 : ℝ) < 1))] with j hj
  intro k hk
  exact hj.le.trans (dyadicPoint_mono (mainBinSet_mem hk).1)

theorem eventually_mainBin_bulk (C : ℝ) :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j,
      dyadicPoint (k + 1) ≤ endpointCenter C (2 ^ j) := by
  filter_upwards [eventually_linear_le_two_pow_sqrt (C * Real.log 2)] with j hj
  intro k hk
  have hpow : (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ Nat.sqrt j ≤ (2 : ℝ) ^ j := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (mainBinSet_mem hk).2
  have hnum : C * Real.log ((2 ^ j : ℕ) : ℝ) * (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ j := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    calc
      C * ((j : ℝ) * Real.log 2) * (2 : ℝ) ^ (k + 1) =
          (2 : ℝ) ^ (k + 1) * ((C * Real.log 2) * j) := by ring
      _ ≤ (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ Nat.sqrt j := mul_le_mul_of_nonneg_left hj (by positivity)
      _ ≤ _ := hpow
  have hdiv : C * Real.log ((2 ^ j : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ 1 / (2 : ℝ) ^ (k + 1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simpa only [one_mul, Nat.cast_pow, Nat.cast_ofNat] using hnum
  exact sub_le_sub_left hdiv 1

end Erdos521
