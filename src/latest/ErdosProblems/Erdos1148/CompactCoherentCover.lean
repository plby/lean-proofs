import ErdosProblems.Erdos1148.FiniteLiftCoverComposition
import ErdosProblems.Erdos1148.FiniteShrinkingBowenCover

/-! # Restricting covers and replacing coherent pieces by compact covers -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem LiftCoverBound.of_cover {η S M : ℝ} {E : Set SL(2, ℝ)} {N : ℕ}
    (B : Fin N → Set SL(2, ℝ)) (hN : (N : ℝ) ≤ M) (hcov : E ⊆ ⋃ i, B i)
    (hB : ∀ i, LiftForwardClose η S (B i)) : LiftCoverBound η S E M := by
  refine ⟨N, fun i => E ∩ B i, hN, ?_, fun i => (hB i).mono Set.inter_subset_right⟩
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun _ => Set.inter_subset_left
  · intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hg)
    exact Set.mem_iUnion.mpr ⟨i, hg, hi⟩

theorem LiftCoverBound.exists_compact_cover {η S M : ℝ} {E : Set SL(2, ℝ)}
    (hE : LiftCoverBound η S E M) (hη : 0 < η) (hηsmall : η ≤ 1 / 2) (hS : 0 ≤ S) :
    ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
      (N : ℝ) ≤ M * 33 ^ 3 ∧ E ⊆ ⋃ i, B i ∧ (∀ i, IsCompact (B i)) ∧
      ∀ i, LiftForwardClose η S (B i) := by
  obtain ⟨N, C, hN, hcov, hC⟩ := hE
  obtain ⟨L, B, hL, hB, hcover, hclose⟩ := exists_shrunk_finite_lift_cover hη hηsmall hη hS C hC
  have hcost : (32 * η / η + 1) ^ 3 = (33 : ℝ) ^ 3 := by
    norm_num [mul_div_assoc, hη.ne']
  rw [hcost] at hL
  rw [hcov] at hcover
  exact ⟨L, B, hL.trans (mul_le_mul_of_nonneg_right hN (by positivity)), hcover, hB, hclose⟩

end Erdos1148.DukeArithmetic
