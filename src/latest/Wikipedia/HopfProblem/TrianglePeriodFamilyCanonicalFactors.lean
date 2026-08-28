import Wikipedia.HopfProblem.TrianglePeriodFamilyAction
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The actual period-family determinant cocycle

The complex factors are extracted from the actual period matrices and dual
integral representation.  The fixed last lattice vector forces every right
block to have second column `e₂`.  This proves the lower-triangular form and
the generator, cusp, and cocycle formulas in Lemmas 9.10(i) and 9.14(i).
-/

noncomputable section

open Set Matrix
open scoped ContDiff MatrixGroups

namespace Wikipedia.HopfProblem.TrianglePeriodFamily

open SpecialPeriods

/-- Every actual dual matrix fixes the distinguished last lattice vector
after extension of scalars.  This follows from the two integral generator
matrices and generation of the whole triangle group. -/
theorem dualComplexMatrix_fixes_delta (g : TriangleGroup) :
    dualComplexMatrix g *ᵥ ![0, 0, 0, 1] = (![0, 0, 0, 1] : Fin 4 → ℂ) := by
  have hg : g ∈ Subgroup.closure
      ({triangleGenerator₁, triangleGenerator₂} : Set TriangleGroup) := by
    rw [triangle_generators_generate]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem h hh =>
    rcases hh with rfl | rfl
    · rw [dualComplexMatrix_generator₁]
      ext i
      fin_cases i <;> norm_num [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        Matrix.cons_val_two, Matrix.cons_val_three]
    · rw [dualComplexMatrix_generator₂]
      ext i
      fin_cases i <;> norm_num [A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        Matrix.cons_val_two, Matrix.cons_val_three]
  | one => rw [dualComplexMatrix_one, Matrix.one_mulVec]
  | mul g h _ _ ihg ihh =>
    rw [dualComplexMatrix_mul, ← Matrix.mulVec_mulVec, ihh, ihg]
  | inv g _ ih =>
    have he := congrArg (fun v : Fin 4 → ℂ => dualComplexMatrix g⁻¹ *ᵥ v) ih
    rw [Matrix.mulVec_mulVec, ← dualComplexMatrix_mul, inv_mul_cancel,
      dualComplexMatrix_one, Matrix.one_mulVec] at he
    exact he.symm

theorem dualComplexMatrix_lastColumn (g : TriangleGroup) (i : Fin 4) :
    dualComplexMatrix g i 3 = (![0, 0, 0, 1] : Fin 4 → ℂ) i := by
  have h := congrFun (dualComplexMatrix_fixes_delta g) i
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_four] using h

namespace Data

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)

@[simp] theorem rightBlock_generator₁ (b : B) :
    D.rightBlock triangleGenerator₁ b = (D.periods.point b).val.R₁ := by
  apply D.rightBlock_eq_of_covariance
  rw [D.covariance₁, dualComplexMatrix_generator₁]
  change (D.periods.point b).val.step₁.matrix * A₁.map (Int.castRingHom ℂ) = _
  rw [PeriodPoint.step₁_matrix _ ((D.periods.point b).val.τ_ne_zero
    (D.periods.point b).property.1), Matrix.mul_assoc]
  have h : (T₁.map (Int.castRingHom ℂ)).transpose * A₁.map (Int.castRingHom ℂ) = 1 := by
    change T₁.transpose.map (Int.castRingHom ℂ) * A₁.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₁.transpose * A₁ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

@[simp] theorem rightBlock_generator₂ (b : B) :
    D.rightBlock triangleGenerator₂ b = (D.periods.point b).val.R₂ := by
  apply D.rightBlock_eq_of_covariance
  rw [D.covariance₂, dualComplexMatrix_generator₂]
  change (D.periods.point b).val.step₂.matrix * A₂.map (Int.castRingHom ℂ) = _
  rw [PeriodPoint.step₂_matrix _ ((D.periods.point b).val.τ_ne_zero
    (D.periods.point b).property.1), Matrix.mul_assoc]
  have h : (T₂.map (Int.castRingHom ℂ)).transpose * A₂.map (Int.castRingHom ℂ) = 1 := by
    change T₂.transpose.map (Int.castRingHom ℂ) * A₂.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₂.transpose * A₂ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

/-- The cusp factor is the identity, directly from the last two columns
of the actual integral cusp matrix. No separate cusp covariance is assumed. -/
@[simp] theorem rightBlock_cusp (b : B) : D.rightBlock triangleCuspGenerator b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rightBlock, dualComplexMatrix, triangleDualRepresentation_cusp_matrix,
      PeriodPoint.matrix, M₀, Matrix.mul_apply, Fin.sum_univ_four]

/-- The fixed dual lattice vector becomes the second unit vector of
every normalized period matrix, including at elliptic points. -/
theorem rightBlock_secondColumn (g : TriangleGroup) (b : B) :
    (fun i => D.rightBlock g b i 1) = (![0, 1] : Fin 2 → ℂ) := by
  ext i
  fin_cases i <;>
    simp [rightBlock, Matrix.mul_apply, Fin.sum_univ_four,
      dualComplexMatrix_lastColumn, PeriodPoint.matrix]

@[simp] theorem rightBlock_zero_one (g : TriangleGroup) (b : B) :
    D.rightBlock g b 0 1 = 0 := congrFun (D.rightBlock_secondColumn g b) 0

@[simp] theorem rightBlock_one_one (g : TriangleGroup) (b : B) :
    D.rightBlock g b 1 1 = 1 := congrFun (D.rightBlock_secondColumn g b) 1

theorem rightBlock_fixes_second (g : TriangleGroup) (b : B) :
    D.rightBlock g b *ᵥ ![0, 1] = (![0, 1] : Fin 2 → ℂ) := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem rightBlock_isLowerTriangular (g : TriangleGroup) (b : B) :
    (D.rightBlock g b).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- For the actual right block the determinant is its first diagonal entry. -/
theorem rightBlock_det_eq_entry (g : TriangleGroup) (b : B) :
    (D.rightBlock g b).det = D.rightBlock g b 0 0 := by
  rw [Matrix.det_fin_two, D.rightBlock_zero_one, D.rightBlock_one_one]
  ring

/-- The source's scalar `r_g`, defined from the actual complex right block. -/
def determinantFactor (g : TriangleGroup) (b : B) : ℂ := (D.rightBlock g b).det

theorem determinantFactor_eq_entry (g : TriangleGroup) (b : B) :
    D.determinantFactor g b = D.rightBlock g b 0 0 := D.rightBlock_det_eq_entry g b

/-- The full lower-triangular matrix formula, with the scalar actually
equal to its determinant. -/
theorem rightBlock_eq_lower (g : TriangleGroup) (b : B) :
    D.rightBlock g b = !![D.determinantFactor g b, 0; D.rightBlock g b 1 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D.determinantFactor_eq_entry]

theorem determinantFactor_ne_zero (g : TriangleGroup) (b : B) :
    D.determinantFactor g b ≠ 0 := D.rightBlock_det_ne_zero g b

@[simp] theorem determinantFactor_one (b : B) : D.determinantFactor 1 b = 1 := by
  simp [determinantFactor]

theorem determinantFactor_mul (g h : TriangleGroup) (b : B) :
    D.determinantFactor (g * h) b =
      D.determinantFactor g (h • b) * D.determinantFactor h b := by
  simp only [determinantFactor, D.rightBlock_mul, Matrix.det_mul]

@[simp] theorem determinantFactor_generator₁ (b : B) :
    D.determinantFactor triangleGenerator₁ b = -1 / (D.periods.point b).val.τ := by
  rw [determinantFactor, D.rightBlock_generator₁, PeriodPoint.det_R₁]

@[simp] theorem determinantFactor_generator₂ (b : B) :
    D.determinantFactor triangleGenerator₂ b = 1 / (D.periods.point b).val.τ := by
  rw [determinantFactor, D.rightBlock_generator₂, PeriodPoint.det_R₂]

@[simp] theorem determinantFactor_cusp (b : B) :
    D.determinantFactor triangleCuspGenerator b = 1 := by
  simp [determinantFactor]

theorem determinantFactor_inv (g : TriangleGroup) (b : B) :
    D.determinantFactor g⁻¹ (g • b) = (D.determinantFactor g b)⁻¹ := by
  have h := congrArg Matrix.det (D.rightBlock_inv_mul g b)
  change (D.rightBlock g⁻¹ (g • b) * D.rightBlock g b).det = (1 : Matrix (Fin 2) (Fin 2) ℂ).det at h
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact eq_inv_of_mul_eq_one_left h

theorem determinantFactor_holomorphic (g : TriangleGroup) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
      (D.determinantFactor g) := by
  change ContMDiff _ _ _ (fun b => (D.rightBlock g b).det)
  simp only [D.rightBlock_det_eq_entry]
  exact D.rightBlock_entry_holomorphic g 0 0

/-- The reciprocal scalar, denoted `ȷ_g` in the source. -/
def inverseDeterminantFactor (g : TriangleGroup) (b : B) : ℂ := (D.determinantFactor g b)⁻¹

theorem inverseDeterminantFactor_ne_zero (g : TriangleGroup) (b : B) :
    D.inverseDeterminantFactor g b ≠ 0 := inv_ne_zero (D.determinantFactor_ne_zero g b)

@[simp] theorem inverseDeterminantFactor_one (b : B) : D.inverseDeterminantFactor 1 b = 1 := by
  simp [inverseDeterminantFactor]

theorem inverseDeterminantFactor_mul (g h : TriangleGroup) (b : B) :
    D.inverseDeterminantFactor (g * h) b =
      D.inverseDeterminantFactor g (h • b) * D.inverseDeterminantFactor h b := by
  simp only [inverseDeterminantFactor, D.determinantFactor_mul, _root_.mul_inv_rev]
  ring

@[simp] theorem inverseDeterminantFactor_generator₁ (b : B) :
    D.inverseDeterminantFactor triangleGenerator₁ b = -(D.periods.point b).val.τ := by
  simp [inverseDeterminantFactor, div_neg]

@[simp] theorem inverseDeterminantFactor_generator₂ (b : B) :
    D.inverseDeterminantFactor triangleGenerator₂ b = (D.periods.point b).val.τ := by
  simp [inverseDeterminantFactor]

@[simp] theorem inverseDeterminantFactor_cusp (b : B) :
    D.inverseDeterminantFactor triangleCuspGenerator b = 1 := by
  simp [inverseDeterminantFactor]

theorem inverseDeterminantFactor_holomorphic (g : TriangleGroup) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
      (D.inverseDeterminantFactor g) :=
  (D.determinantFactor_holomorphic g).inv₀ (D.determinantFactor_ne_zero g)

end Data

end Wikipedia.HopfProblem.TrianglePeriodFamily
