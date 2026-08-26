/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform normalized moments for the central dyadic interval.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.MainBinBulk
import ErdosProblems.Erdos521.IcoPartitionMoments

namespace Erdos521

open MeasureTheory Filter

theorem central_bin_endpoints_strict {j : ℕ} (hj : 9 ≤ j) : Nat.sqrt j < j - Nat.sqrt j := by
  have hr : 3 ≤ Nat.sqrt j := Nat.le_sqrt.mpr hj
  have hgap : 2 * Nat.sqrt j + 1 ≤ j := by nlinarith [Nat.sqrt_le' j]
  omega

theorem eventually_central_interval_moments (p : ℕ) (hp : 1 ≤ p) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ j : ℕ in atTop,
      (∫ ε, (intervalRootCount ε (2 ^ j) (dyadicPoint (Nat.sqrt j))
        (dyadicPoint (j - Nat.sqrt j)) : ℝ) ^ p ∂sequenceLaw) ≤ (j : ℝ) ^ p * B := by
  obtain ⟨B, hB, hmom⟩ := eventually_dyadic_interval_moments p hp
  have hdegree : Tendsto (fun j : ℕ ↦ (2 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hdegree.eventually hmom, eventually_mainBin_lower,
    eventually_mainBin_bulk (localMomentBulkConstant p), eventually_ge_atTop 9] with j hj hl hu hj₉
  have hcell (k : ℕ) (hk : k ∈ Finset.Ico (Nat.sqrt j) (j - Nat.sqrt j)) :
      (∫ ε, (intervalRootCount ε (2 ^ j) (dyadicPoint k) (dyadicPoint (k + 1)) : ℝ) ^ p ∂sequenceLaw) ≤ B :=
    hj k (hl k hk) (hu k hk)
  have h := integral_intervalRootCount_Ico_pow_le (2 ^ j) (Nat.sqrt j) (j - Nat.sqrt j) p
    (central_bin_endpoints_strict hj₉) hp dyadicPoint dyadicPoint_mono hcell
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ hB.le
  apply pow_le_pow_left₀ (Nat.cast_nonneg _)
  exact_mod_cast (show j - Nat.sqrt j - Nat.sqrt j ≤ j by omega)

end Erdos521
