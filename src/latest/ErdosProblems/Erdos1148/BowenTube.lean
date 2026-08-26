import ErdosProblems.Erdos1148.RelativeFlow

/-! # Entrywise Bowen tubes for the diagonal flow -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def EntryBowenTube (η δ : ℝ) (g : SL(2, ℝ)) : Prop :=
  |g 0 0 - 1| ≤ η ∧ |g 0 1| ≤ δ ∧ |g 1 0| ≤ δ ∧ |g 1 1 - 1| ≤ η

lemma diagonalFlow_conjugate_matrix (g : SL(2, ℝ)) (t : ℝ) :
    ((diagonalFlow (-t) * g * diagonalFlow t : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![g 0 0, g 0 1 * Real.exp (-t); g 1 0 * Real.exp t, g 1 1] := by
  simpa only [sub_self, zero_div, Real.exp_zero, mul_one, add_self_div_two] using
    diagonalFlow_relative_matrix g t t

lemma entryCloseOne_diagonalFlow_conjugate_iff (η : ℝ) (g : SL(2, ℝ)) (t : ℝ) :
    EntryCloseOne η (diagonalFlow (-t) * g * diagonalFlow t) ↔
      |g 0 0 - 1| ≤ η ∧ |g 0 1| * Real.exp (-t) ≤ η ∧
        |g 1 0| * Real.exp t ≤ η ∧ |g 1 1 - 1| ≤ η := by
  have h00 : (diagonalFlow (-t) * g * diagonalFlow t) 0 0 = g 0 0 := by
    simpa only [Matrix.of_apply, Matrix.cons_val_zero] using
      congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ => m 0 0) (diagonalFlow_conjugate_matrix g t)
  have h01 : (diagonalFlow (-t) * g * diagonalFlow t) 0 1 = g 0 1 * Real.exp (-t) :=
    congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ => m 0 1) (diagonalFlow_conjugate_matrix g t)
  have h10 : (diagonalFlow (-t) * g * diagonalFlow t) 1 0 = g 1 0 * Real.exp t :=
    congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ => m 1 0) (diagonalFlow_conjugate_matrix g t)
  have h11 : (diagonalFlow (-t) * g * diagonalFlow t) 1 1 = g 1 1 := by
    simpa only [Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one] using
      congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ => m 1 1) (diagonalFlow_conjugate_matrix g t)
  simp only [EntryCloseOne, h00, h01, h10, h11, abs_mul, abs_of_pos (Real.exp_pos _)]

theorem entryBowenTube_iff_flow_closeness {η N : ℝ} (hN : 0 ≤ N) (g : SL(2, ℝ)) :
    EntryBowenTube η (η * Real.exp (-N)) g ↔
      ∀ t ∈ Set.Icc (-N) N, EntryCloseOne η (diagonalFlow (-t) * g * diagonalFlow t) := by
  have hcoords := entryCloseOne_diagonalFlow_conjugate_iff η g
  constructor
  · rintro ⟨ha, hb, hc, hd⟩ t ht
    have hη : 0 ≤ η := (abs_nonneg _).trans ha
    rw [hcoords]
    refine ⟨ha, ?_, ?_, hd⟩
    · calc
        _ ≤ (η * Real.exp (-N)) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        _ = η * Real.exp (-N - t) := by rw [mul_assoc, ← Real.exp_add]; congr 2 <;> ring
        _ ≤ η * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by linarith [ht.1])) hη
        _ = η := mul_one _
    · calc
        _ ≤ (η * Real.exp (-N)) * Real.exp t :=
          mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
        _ = η * Real.exp (-N + t) := by rw [mul_assoc, ← Real.exp_add]
        _ ≤ η * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by linarith [ht.2])) hη
        _ = η := mul_one _
  · intro h
    have hminus := (hcoords (-N)).mp (h (-N) ⟨le_rfl, by linarith⟩)
    have hplus := (hcoords N).mp (h N ⟨by linarith, le_rfl⟩)
    refine ⟨hminus.1, ?_, ?_, hminus.2.2.2⟩
    · have hm := mul_le_mul_of_nonneg_right hminus.2.1 (Real.exp_pos (-N)).le
      simpa only [neg_neg, mul_assoc, ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, mul_one] using hm
    · have hm := mul_le_mul_of_nonneg_right hplus.2.2.1 (Real.exp_pos (-N)).le
      simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] using hm

end Erdos1148.DukeArithmetic
