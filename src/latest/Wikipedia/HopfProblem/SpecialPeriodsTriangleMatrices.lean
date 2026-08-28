import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The explicit real matrices for the (3,4,∞) triangle group

These are determinant-one matrices with their actual multiplication laws.
The cube and fourth-power relations hold up to the central matrix `-1`,
and their product is the inverse cusp translation.  No discreteness or
fundamental-domain assertion is included among the hypotheses.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The width of the parabolic translation in the paper's normalization. -/
def width : ℝ := 1 + Real.sqrt 2

theorem width_pos : 0 < width := by
  unfold width
  positivity

theorem one_lt_width : 1 < width := by
  unfold width
  have : 0 < Real.sqrt 2 := by positivity
  linarith

theorem width_ne_zero : width ≠ 0 := width_pos.ne'

theorem width_sq : width ^ 2 = 2 * width + 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  unfold width
  nlinarith

theorem width_polynomial : width ^ 2 - 2 * width - 1 = 0 := by
  linear_combination width_sq

theorem width_sub_one_sq : (width - 1) ^ 2 = 2 := by
  nlinarith [width_sq]

/-- The order-three elliptic generator, before quotienting by the center. -/
def generatorOneSL : SL(2, ℝ) :=
  ⟨!![0, -1; 1, 1], by norm_num [Matrix.det_fin_two_of]⟩

/-- The order-four elliptic generator, before quotienting by the center. -/
def generatorTwoSL : SL(2, ℝ) :=
  ⟨!![1, width + 1; -1, -width], by simp [Matrix.det_fin_two_of]⟩

/-- The product of the elliptic generators translates by positive width. -/
def cuspInverseSL : SL(2, ℝ) :=
  ⟨!![1, width; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The cusp generator itself translates by negative width. -/
def cuspSL : SL(2, ℝ) := cuspInverseSL⁻¹

@[simp] theorem coe_generatorOneSL :
    (generatorOneSL : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 1] := rfl

@[simp] theorem coe_generatorTwoSL :
    (generatorTwoSL : Matrix (Fin 2) (Fin 2) ℝ) = !![1, width + 1; -1, -width] := rfl

@[simp] theorem coe_cuspInverseSL :
    (cuspInverseSL : Matrix (Fin 2) (Fin 2) ℝ) = !![1, width; 0, 1] := rfl

theorem coe_generatorOneSL_inv :
    ((generatorOneSL⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 1; -1, 0] := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem coe_generatorTwoSL_inv :
    ((generatorTwoSL⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-width, -(width + 1); 1, 1] := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp] theorem coe_cuspSL :
    (cuspSL : Matrix (Fin 2) (Fin 2) ℝ) = !![1, -width; 0, 1] := by
  simp [cuspSL, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem coe_generatorOneSL_sq :
    ((generatorOneSL ^ 2 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-1, -1; 1, 0] := by
  norm_num [Matrix.SpecialLinearGroup.coe_pow, pow_two, Matrix.mul_fin_two]

theorem generatorOneSL_cube : generatorOneSL ^ 3 = -1 := by
  apply Subtype.ext
  norm_num [Matrix.SpecialLinearGroup.coe_pow, pow_succ, Matrix.mul_fin_two,
    Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem coe_generatorTwoSL_sq :
    ((generatorTwoSL ^ 2 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-width, -2 * width; width - 1, width] := by
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_generatorTwoSL, pow_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> nlinarith [width_sq]

theorem generatorTwoSL_fourth : generatorTwoSL ^ 4 = -1 := by
  have hsq : (generatorTwoSL ^ 2) ^ 2 = -1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_generatorTwoSL_sq,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      pow_two, Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> nlinarith [width_sq]
  simpa only [← pow_mul] using hsq

/-- The precise parabolic relation in `SL₂(ℝ)`. -/
theorem generatorOneSL_mul_generatorTwoSL :
    generatorOneSL * generatorTwoSL = cuspInverseSL := by
  apply Subtype.ext
  simp

theorem generatorOneSL_mul_generatorTwoSL_mul_cuspSL :
    generatorOneSL * generatorTwoSL * cuspSL = 1 := by
  rw [generatorOneSL_mul_generatorTwoSL, cuspSL, mul_inv_cancel]

theorem cuspSL_inv : cuspSL⁻¹ = cuspInverseSL := inv_inv _

theorem generatorOneSL_trace :
    (generatorOneSL : Matrix (Fin 2) (Fin 2) ℝ).trace = 1 := by
  simp [Matrix.trace_fin_two]

theorem generatorTwoSL_trace :
    (generatorTwoSL : Matrix (Fin 2) (Fin 2) ℝ).trace = -Real.sqrt 2 := by
  simp [Matrix.trace_fin_two, width]

theorem cuspInverseSL_trace :
    (cuspInverseSL : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 := by
  norm_num [Matrix.trace_fin_two]

theorem cuspSL_trace : (cuspSL : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 := by
  norm_num [Matrix.trace_fin_two]

theorem generatorOneSL_isElliptic :
    (generatorOneSL : Matrix (Fin 2) (Fin 2) ℝ).IsElliptic := by
  norm_num [Matrix.IsElliptic, Matrix.discr_fin_two, generatorOneSL_trace]

theorem generatorTwoSL_isElliptic :
    (generatorTwoSL : Matrix (Fin 2) (Fin 2) ℝ).IsElliptic := by
  norm_num [Matrix.IsElliptic, Matrix.discr_fin_two, generatorTwoSL_trace]
  nlinarith [width_sub_one_sq]

theorem cuspInverseSL_isParabolic :
    (cuspInverseSL : Matrix (Fin 2) (Fin 2) ℝ).IsParabolic := by
  rw [Matrix.isParabolic_iff_of_upperTriangular (by simp)]
  simp [width_ne_zero]

theorem cuspSL_isParabolic :
    (cuspSL : Matrix (Fin 2) (Fin 2) ℝ).IsParabolic := by
  rw [Matrix.isParabolic_iff_of_upperTriangular (by simp)]
  simp [width_ne_zero]

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
