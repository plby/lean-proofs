import ErdosProblems.Erdos1148.BowenTube

/-! # One-sided Bowen tubes for the diagonal flow -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def EntryForwardBowenTube (η δ : ℝ) (g : SL(2, ℝ)) : Prop :=
  EntryCloseOne η g ∧ |g 1 0| ≤ δ

theorem entryForwardBowenTube_iff_flow_closeness {η S : ℝ} (hS : 0 ≤ S) (g : SL(2, ℝ)) :
    EntryForwardBowenTube η (η * Real.exp (-S)) g ↔
      ∀ t ∈ Set.Icc 0 S, EntryCloseOne η (diagonalFlow (-t) * g * diagonalFlow t) := by
  constructor
  · rintro ⟨hg, hlow⟩ t ht
    have hη : 0 ≤ η := (abs_nonneg _).trans hg.1
    rw [entryCloseOne_diagonalFlow_conjugate_iff]
    refine ⟨hg.1, ?_, ?_, hg.2.2.2⟩
    · calc
        _ ≤ η * 1 := mul_le_mul hg.2.1
          (Real.exp_le_one_iff.mpr (by linarith [ht.1])) (Real.exp_pos _).le hη
        _ = η := mul_one _
    · calc
        _ ≤ (η * Real.exp (-S)) * Real.exp t :=
          mul_le_mul_of_nonneg_right hlow (Real.exp_pos _).le
        _ = η * Real.exp (-S + t) := by rw [mul_assoc, ← Real.exp_add]
        _ ≤ η * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by linarith [ht.2])) hη
        _ = η := mul_one _
  · intro h
    have hzero := h 0 ⟨le_rfl, hS⟩
    simp only [neg_zero, diagonalFlow_zero, one_mul, mul_one] at hzero
    have hlast := (entryCloseOne_diagonalFlow_conjugate_iff η g S).mp (h S ⟨hS, le_rfl⟩)
    refine ⟨hzero, ?_⟩
    have hm := mul_le_mul_of_nonneg_right hlast.2.2.1 (Real.exp_pos (-S)).le
    simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] using hm

end Erdos1148.DukeArithmetic
