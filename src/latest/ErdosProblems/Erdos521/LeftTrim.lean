/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The discarded dyadic bins toward the compact interior are negligible almost surely.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.CentralIntervalMoments
import ErdosProblems.Erdos521.FourthMomentNegligible

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem eventually_left_trim_fourth_moment :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ j : ℕ in atTop,
      (∫ ε, (intervalRootCount ε (2 ^ j) (dyadicPoint 4) (dyadicPoint (Nat.sqrt j)) : ℝ) ^ 4 ∂sequenceLaw) ≤
        B * (j : ℝ) ^ 2 := by
  obtain ⟨B, hB, hmom⟩ := eventually_dyadic_interval_moments 4 (by norm_num)
  have hdegree : Tendsto (fun j : ℕ ↦ (2 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hdegree.eventually hmom, eventually_mainBin_bulk (localMomentBulkConstant 4),
    eventually_ge_atTop 25] with j hj hbulk hj₂₅
  have hr : 5 ≤ Nat.sqrt j := Nat.le_sqrt.mpr hj₂₅
  have hrS : Nat.sqrt j ∈ mainBinSet j :=
    Finset.mem_Ico.mpr ⟨le_rfl, central_bin_endpoints_strict (by omega)⟩
  have hupper : dyadicPoint (Nat.sqrt j) ≤ endpointCenter (localMomentBulkConstant 4) (2 ^ j) :=
    (dyadicPoint_mono (Nat.le_succ _)).trans (hbulk (Nat.sqrt j) hrS)
  have hcell (k : ℕ) (hk : k ∈ Finset.Ico 4 (Nat.sqrt j)) :
      (∫ ε, (intervalRootCount ε (2 ^ j) (dyadicPoint k) (dyadicPoint (k + 1)) : ℝ) ^ 4 ∂sequenceLaw) ≤ B := by
    obtain ⟨hk₀, hk₁⟩ := Finset.mem_Ico.mp hk
    apply hj k
    · exact (by norm_num [dyadicPoint] : (9 / 10 : ℝ) ≤ dyadicPoint 4).trans (dyadicPoint_mono hk₀)
    · exact (dyadicPoint_mono (by omega : k + 1 ≤ Nat.sqrt j)).trans hupper
  have h := integral_intervalRootCount_Ico_pow_le (2 ^ j) 4 (Nat.sqrt j) 4 (by omega) (by norm_num)
    dyadicPoint dyadicPoint_mono hcell
  apply h.trans
  have hpow : (((Nat.sqrt j - 4 : ℕ) : ℝ)) ^ 4 ≤ (j : ℝ) ^ 2 := by
    have hsmall : ((Nat.sqrt j - 4 : ℕ) : ℝ) ≤ Nat.sqrt j := by exact_mod_cast Nat.sub_le (Nat.sqrt j) 4
    have hroot : (Nat.sqrt j : ℝ) ^ 2 ≤ j := by exact_mod_cast Nat.sqrt_le' j
    calc
      _ ≤ (Nat.sqrt j : ℝ) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hsmall 4
      _ = ((Nat.sqrt j : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ (j : ℝ) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hroot 2
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hpow hB.le

theorem ae_left_trim_div_index_tendsto_zero :
    ∀ᵐ ε ∂sequenceLaw, Tendsto (fun j : ℕ ↦
      (intervalRootCount ε (2 ^ j) (dyadicPoint 4) (dyadicPoint (Nat.sqrt j)) : ℝ) / j) atTop (𝓝 0) := by
  obtain ⟨B, _, hB⟩ := eventually_left_trim_fourth_moment
  exact ae_nat_div_tendsto_zero_of_fourth_moment sequenceLaw
    (fun j ε ↦ intervalRootCount ε (2 ^ j) (dyadicPoint 4) (dyadicPoint (Nat.sqrt j)))
    (fun j ↦ intervalRootCount_pow_integrable (2 ^ j) 4 _ _) ⟨B, hB⟩

end Erdos521
