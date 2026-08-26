/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The actual central count and the capped sum can differ only through local errors or shared roots.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.CentralStatistics
import ErdosProblems.Erdos521.IcoRootPartition

namespace Erdos521

open MeasureTheory

noncomputable def binComparisonException (j k : ℕ) : Set (ℕ → ℝ) := {ε |
  intervalRootCount ε (2 ^ j) (dyadicPoint k) (dyadicPoint (k + 1)) ≠
    min (windowGridSignChanges ε (dyadicCoefficientWindow (2 ^ j) k (windowWidthScale j))
      (dyadicFineGrid j k) (fineGridLength j)) (windowCapScale j) ∨
    powerSum ε (2 ^ j + 1) (dyadicPoint k) = 0}

theorem central_disagreement_ae_cover {j : ℕ} (hj : 9 ≤ j) :
    ∀ᵐ ε ∂sequenceLaw, centralRootCount ε j ≠ centralCappedCount ε j →
      ε ∈ ⋃ k ∈ mainBinSet j, binComparisonException j k := by
  filter_upwards [ae_sequence_signs] with ε hsigns hneq
  by_contra hbad
  have hconst : ε 0 ≠ 0 := by rcases hsigns 0 with h | h <;> simp [h]
  have hzero (k : ℕ) (hk : k ∈ mainBinSet j) : powerSum ε (2 ^ j + 1) (dyadicPoint k) ≠ 0 := by
    intro hz
    apply hbad
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, Or.inr hz⟩⟩
  have hlocal (k : ℕ) (hk : k ∈ mainBinSet j) :
      intervalRootCount ε (2 ^ j) (dyadicPoint k) (dyadicPoint (k + 1)) =
        min (windowGridSignChanges ε (dyadicCoefficientWindow (2 ^ j) k (windowWidthScale j))
          (dyadicFineGrid j k) (fineGridLength j)) (windowCapScale j) := by
    by_contra hne
    apply hbad
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, Or.inl hne⟩⟩
  apply hneq
  have hpartition := intervalRootCount_Ico_eq_sum_of_nonzero_grid ε (2 ^ j) hconst
    (Nat.sqrt j) (j - Nat.sqrt j) (central_bin_endpoints_strict hj) dyadicPoint dyadicPoint_mono hzero
  unfold centralRootCount centralCappedCount
  rw [hpartition]
  unfold cappedCentralNatSum
  exact Finset.sum_congr rfl hlocal

end Erdos521
