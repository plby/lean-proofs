import Wikipedia.HopfProblem.SpecialPeriodsTriangleMatrices

/-!
# The matrix recurrence in the Shimizu--Leutbecher argument

Conjugating a translation by the previous matrix squares its lower-left
entry.  All matrices here are actual elements of `SL(2, ℝ)`.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- Translation by an arbitrary real width, as a determinant-one matrix. -/
def shimizuTranslation (w : ℝ) : SL(2, ℝ) :=
  ⟨!![1, w; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] theorem coe_shimizuTranslation (w : ℝ) :
    (shimizuTranslation w : Matrix (Fin 2) (Fin 2) ℝ) = !![1, w; 0, 1] := rfl

theorem shimizuTranslation_width : shimizuTranslation width = cuspInverseSL := rfl

/-- The exact conjugation formula driving the discreteness contradiction. -/
theorem shimizu_conjugate_matrix (w : ℝ) (A : SL(2, ℝ)) :
    ((A * shimizuTranslation w * A⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1 - w * A 0 0 * A 1 0, w * (A 0 0) ^ 2;
        -w * (A 1 0) ^ 2, 1 + w * A 0 0 * A 1 0] := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 :=
    (Matrix.det_fin_two A.val).symm.trans A.property
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    coe_shimizuTranslation, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hdet]

/-- The sequence stays in any subgroup containing its first element and the translation. -/
def shimizuSequence (w : ℝ) (A : SL(2, ℝ)) : ℕ → SL(2, ℝ)
  | 0 => A
  | n + 1 => shimizuSequence w A n * shimizuTranslation w * (shimizuSequence w A n)⁻¹

@[simp] theorem shimizuSequence_zero (w : ℝ) (A : SL(2, ℝ)) :
    shimizuSequence w A 0 = A := rfl

theorem shimizuSequence_succ (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    shimizuSequence w A (n + 1) =
      shimizuSequence w A n * shimizuTranslation w * (shimizuSequence w A n)⁻¹ := rfl

theorem shimizuSequence_mem (Γ : Subgroup (SL(2, ℝ))) (w : ℝ) (A : SL(2, ℝ))
    (hT : shimizuTranslation w ∈ Γ) (hA : A ∈ Γ) (n : ℕ) : shimizuSequence w A n ∈ Γ := by
  induction n with
  | zero => exact hA
  | succ n ih => exact Γ.mul_mem (Γ.mul_mem ih hT) (Γ.inv_mem ih)

theorem shimizuSequence_succ_matrix (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    (shimizuSequence w A (n + 1) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1 - w * shimizuSequence w A n 0 0 * shimizuSequence w A n 1 0,
        w * (shimizuSequence w A n 0 0) ^ 2;
        -w * (shimizuSequence w A n 1 0) ^ 2,
        1 + w * shimizuSequence w A n 0 0 * shimizuSequence w A n 1 0] :=
  shimizu_conjugate_matrix w (shimizuSequence w A n)

theorem shimizuSequence_succ_zero_zero (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    shimizuSequence w A (n + 1) 0 0 =
      1 - shimizuSequence w A n 0 0 * (w * shimizuSequence w A n 1 0) := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0)
    (shimizuSequence_succ_matrix w A n)
  simpa only [Matrix.of_apply, Matrix.cons_val_zero, mul_left_comm, mul_assoc] using h

theorem shimizuSequence_succ_zero_one (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    shimizuSequence w A (n + 1) 0 1 = w * (shimizuSequence w A n 0 0) ^ 2 := by
  simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1)
    (shimizuSequence_succ_matrix w A n)

theorem shimizuSequence_succ_one_zero (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    shimizuSequence w A (n + 1) 1 0 = -w * (shimizuSequence w A n 1 0) ^ 2 := by
  simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0)
    (shimizuSequence_succ_matrix w A n)

theorem shimizuSequence_succ_one_one (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    shimizuSequence w A (n + 1) 1 1 =
      1 + shimizuSequence w A n 0 0 * (w * shimizuSequence w A n 1 0) := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1)
    (shimizuSequence_succ_matrix w A n)
  simpa only [Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero, mul_left_comm,
    mul_assoc] using h

theorem shimizuSequence_succ_scaled_lower_left (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    w * shimizuSequence w A (n + 1) 1 0 = -(w * shimizuSequence w A n 1 0) ^ 2 := by
  rw [shimizuSequence_succ_one_zero]
  ring

theorem shimizuSequence_lower_left_ne_zero (w : ℝ) (A : SL(2, ℝ))
    (hw : w ≠ 0) (hA : A 1 0 ≠ 0) (n : ℕ) : shimizuSequence w A n 1 0 ≠ 0 := by
  induction n with
  | zero => exact hA
  | succ n ih =>
    rw [shimizuSequence_succ_one_zero]
    exact mul_ne_zero (neg_ne_zero.mpr hw) (pow_ne_zero 2 ih)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
