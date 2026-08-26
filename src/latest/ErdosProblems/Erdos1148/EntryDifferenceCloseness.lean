import ErdosProblems.Erdos1148.RotationEntryBounds

/-! # Entrywise matrix differences control relative group distance on bounded frames -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma inverse_entries_bound {A : ℝ} (g : SL(2, ℝ))
    (hg : ∀ i j : Fin 2, |g i j| ≤ A) : ∀ i j : Fin 2, |g⁻¹ i j| ≤ A := by
  intro i j
  fin_cases i <;> fin_cases j
  · change |g⁻¹ 0 0| ≤ A
    simpa only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero] using hg 1 1
  · change |g⁻¹ 0 1| ≤ A
    simpa only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      abs_neg] using hg 0 1
  · change |g⁻¹ 1 0| ≤ A
    simpa only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      abs_neg] using hg 1 0
  · change |g⁻¹ 1 1| ≤ A
    simpa only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one] using hg 0 0

theorem entryCloseOne_of_entry_differences {A δ η : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hscale : 2 * A * δ ≤ η) (g h : SL(2, ℝ))
    (hg : ∀ i j : Fin 2, |g i j| ≤ A) (hdiff : ∀ i j : Fin 2, |h i j - g i j| ≤ δ) :
    EntryCloseOne η (g⁻¹ * h) := by
  have hinv : ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) *
      (g : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have heq : ((g⁻¹ * h : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 1 =
      ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) *
        ((h : Matrix (Fin 2) (Fin 2) ℝ) - (g : Matrix (Fin 2) (Fin 2) ℝ)) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, mul_sub, hinv]
  apply (entryCloseOne_iff_entries η (g⁻¹ * h)).mpr
  intro i j
  change |((((g⁻¹ * h : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 1) i j)| ≤ η
  rw [heq]
  exact (matrix_two_mul_entry_bound _ _ hA hδ (inverse_entries_bound g hg) hdiff i j).trans hscale

end Erdos1148.DukeArithmetic
