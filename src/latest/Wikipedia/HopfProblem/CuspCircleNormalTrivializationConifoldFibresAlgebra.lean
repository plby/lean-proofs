import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldAlgebra

/-!
# Exact fibres and elementary surjectivity of the small-resolution matrices

Away from the zero normal vector, equality of the original matrices
determines exactly the original same-chart or cross-chart identification.
Every determinant-zero matrix is explicitly represented in one of these
two charts by choosing a nonzero entry in its first row, or the upper
chart when that row vanishes.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold

open ConifoldStandardBoundary

theorem lowerMatrix_eq_iff (a b : ℂ) (p q : ℂ × ℂ) (hp : p ≠ 0) :
    lowerMatrix a p = lowerMatrix b q ↔ a = b ∧ p = q := by
  constructor
  · intro h
    have hpq : p = q := Prod.ext
      (congrArg (fun M : MatrixSpace => M 0 0) h)
      (congrArg (fun M : MatrixSpace => M 0 1) h)
    subst q
    have h₀ : a * p.1 = b * p.1 := congrArg (fun M : MatrixSpace => M 1 0) h
    have h₁ : a * p.2 = b * p.2 := congrArg (fun M : MatrixSpace => M 1 1) h
    by_cases hp₀ : p.1 = 0
    · have hp₁ : p.2 ≠ 0 := fun he => hp (Prod.ext hp₀ he)
      exact ⟨mul_right_cancel₀ hp₁ h₁, rfl⟩
    · exact ⟨mul_right_cancel₀ hp₀ h₀, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem upperMatrix_eq_iff (a b : ℂ) (p q : ℂ × ℂ) (hp : p ≠ 0) :
    upperMatrix a p = upperMatrix b q ↔ a = b ∧ p = q := by
  constructor
  · intro h
    have hpq : p = q := Prod.ext
      (congrArg (fun M : MatrixSpace => M 1 0) h)
      (congrArg (fun M : MatrixSpace => M 1 1) h)
    subst q
    have h₀ : a * p.1 = b * p.1 := congrArg (fun M : MatrixSpace => M 0 0) h
    have h₁ : a * p.2 = b * p.2 := congrArg (fun M : MatrixSpace => M 0 1) h
    by_cases hp₀ : p.1 = 0
    · have hp₁ : p.2 ≠ 0 := fun he => hp (Prod.ext hp₀ he)
      exact ⟨mul_right_cancel₀ hp₁ h₁, rfl⟩
    · exact ⟨mul_right_cancel₀ hp₀ h₀, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Equality across the two original charts forces precisely their actual transition. -/
theorem lowerMatrix_eq_upperMatrix_iff (a b : ℂ) (p q : ℂ × ℂ) (hp : p ≠ 0) :
    lowerMatrix a p = upperMatrix b q ↔
      a ≠ 0 ∧ b = a⁻¹ ∧ q = (a * p.1, a * p.2) := by
  constructor
  · intro h
    have h₀₀ : p.1 = b * q.1 := congrArg (fun M : MatrixSpace => M 0 0) h
    have h₀₁ : p.2 = b * q.2 := congrArg (fun M : MatrixSpace => M 0 1) h
    have h₁₀ : a * p.1 = q.1 := congrArg (fun M : MatrixSpace => M 1 0) h
    have h₁₁ : a * p.2 = q.2 := congrArg (fun M : MatrixSpace => M 1 1) h
    have hba : b * a = 1 := by
      by_cases hp₀ : p.1 = 0
      · have hp₁ : p.2 ≠ 0 := fun he => hp (Prod.ext hp₀ he)
        apply mul_right_cancel₀ hp₁
        calc
          (b * a) * p.2 = b * q.2 := by rw [mul_assoc, h₁₁]
          _ = p.2 := h₀₁.symm
          _ = 1 * p.2 := (one_mul p.2).symm
      · apply mul_right_cancel₀ hp₀
        calc
          (b * a) * p.1 = b * q.1 := by rw [mul_assoc, h₁₀]
          _ = p.1 := h₀₀.symm
          _ = 1 * p.1 := (one_mul p.1).symm
    have ha : a ≠ 0 := by
      intro ha
      simp [ha] at hba
    have hb : b = a⁻¹ := by
      calc
        b = (b * a) * a⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]
        _ = a⁻¹ := by rw [hba, one_mul]
    exact ⟨ha, hb, Prod.ext h₁₀.symm h₁₁.symm⟩
  · rintro ⟨ha, rfl, rfl⟩
    exact (upperMatrix_transition a ha p).symm

/-- Every genuine determinant-zero matrix has one of the two literal chart forms. -/
theorem exists_matrix_chart_of_det_zero (M : MatrixSpace) (hdet : M.det = 0) :
    (∃ a : ℂ, ∃ p : ℂ × ℂ, lowerMatrix a p = M) ∨
      (∃ b : ℂ, ∃ p : ℂ × ℂ, upperMatrix b p = M) := by
  have hcross : M 0 0 * M 1 1 = M 0 1 * M 1 0 := by
    exact sub_eq_zero.mp (by simpa only [Matrix.det_fin_two] using hdet)
  by_cases h₀₀ : M 0 0 = 0
  · by_cases h₀₁ : M 0 1 = 0
    · right
      refine ⟨0, (M 1 0, M 1 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperMatrix, h₀₀, h₀₁]
    · left
      have h₁₀ : M 1 0 = 0 :=
        (mul_eq_zero.mp (by simpa only [h₀₀, zero_mul] using hcross.symm)).resolve_left h₀₁
      refine ⟨M 1 1 / M 0 1, (M 0 0, M 0 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lowerMatrix, h₀₀, h₀₁, h₁₀]
  · left
    refine ⟨M 1 0 / M 0 0, (M 0 0, M 0 1), ?_⟩
    have hlast : M 1 0 / M 0 0 * M 0 1 = M 1 1 := by
      rw [div_mul_eq_mul_div, div_eq_iff h₀₀]
      simpa only [mul_comm] using hcross.symm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerMatrix, h₀₀, hlast]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold
