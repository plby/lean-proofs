/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos957.HullOrder

/-!
# Orthogonal frames from strict exposing functionals
-/

open scoped RealInnerProductSpace
open Set

noncomputable section

namespace Erdos957StrictFrame

open Erdos957

abbrev Point := Erdos957.Point

/-- The Riesz vector representing a real continuous linear functional. -/
noncomputable def dualVector (l : Point →L[ℝ] ℝ) : Point :=
  (InnerProductSpace.toDual ℝ Point).symm l

@[simp] theorem inner_dualVector (l : Point →L[ℝ] ℝ) (x : Point) :
    inner ℝ (dualVector l) x = l x := by
  exact InnerProductSpace.toDual_symm_apply

theorem dualVector_ne_zero {l : Point →L[ℝ] ℝ} (hl : l ≠ 0) :
    dualVector l ≠ 0 := by
  intro hv
  have h := congrArg (fun v : Point ↦ (InnerProductSpace.toDual ℝ Point) v) hv
  exact hl (by simpa [dualVector] using h)

/-- The unit Riesz vector. -/
noncomputable def unitDual (l : Point →L[ℝ] ℝ) : Point :=
  ‖dualVector l‖⁻¹ • dualVector l

theorem norm_unitDual {l : Point →L[ℝ] ℝ} (hl : l ≠ 0) :
    ‖unitDual l‖ = 1 := by
  rw [unitDual, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (dualVector_ne_zero hl)

/-- The standard orientation induced by the coordinate orthonormal basis. -/
local instance pointFinrankFact : Fact (Module.finrank ℝ Point = 2) :=
  ⟨by simp [Point, finrank_euclideanSpace]⟩

noncomputable def pointOrientation : Orientation ℝ Point (Fin 2) :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation

/-- An orthonormal frame whose second basis vector points opposite to the
Riesz vector of `l`. -/
noncomputable def supportBasisVector (l : Point →L[ℝ] ℝ) (i : Fin 2) : Point :=
  ![pointOrientation.rightAngleRotation (-unitDual l), -unitDual l] i

theorem supportBasisVector_orthonormal {l : Point →L[ℝ] ℝ} (hl : l ≠ 0) :
    Orthonormal ℝ (supportBasisVector l) := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j
  · change inner ℝ (pointOrientation.rightAngleRotation (-unitDual l))
      (pointOrientation.rightAngleRotation (-unitDual l)) = 1
    rw [pointOrientation.rightAngleRotation.inner_map_map]
    rw [real_inner_self_eq_norm_sq, norm_neg, norm_unitDual hl]
    norm_num
  · change inner ℝ (pointOrientation.rightAngleRotation (-unitDual l))
      (-unitDual l) = 0
    exact pointOrientation.inner_rightAngleRotation_self (-unitDual l)
  · change inner ℝ (-unitDual l)
      (pointOrientation.rightAngleRotation (-unitDual l)) = 0
    rw [real_inner_comm]
    exact pointOrientation.inner_rightAngleRotation_self (-unitDual l)
  · change inner ℝ (-unitDual l) (-unitDual l) = 1
    rw [real_inner_self_eq_norm_sq, norm_neg, norm_unitDual hl]
    norm_num

/-- The orthonormal basis determined by a nonzero functional. -/
noncomputable def supportOrthonormalBasis (l : Point →L[ℝ] ℝ) (hl : l ≠ 0) :
    OrthonormalBasis (Fin 2) ℝ Point := by
  have hon : Orthonormal ℝ (supportBasisVector l) :=
    supportBasisVector_orthonormal hl
  have hspan : Submodule.span ℝ (Set.range (supportBasisVector l)) = ⊤ :=
    hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by
      simp [finrank_euclideanSpace])
  exact OrthonormalBasis.mk hon hspan.ge

/-- Coordinate isometry associated to a strict exposing functional. -/
noncomputable def supportFrame (l : Point →L[ℝ] ℝ) (hl : l ≠ 0) :
    Point ≃ₗᵢ[ℝ] Point :=
  (supportOrthonormalBasis l hl).repr

/-- A vector on which `l` is negative has strictly positive second
coordinate in the exposing frame. -/
theorem supportFrame_apply_one_pos {l : Point →L[ℝ] ℝ} (hl : l ≠ 0)
    {x : Point} (hx : l x < 0) :
    0 < supportFrame l hl x 1 := by
  rw [supportFrame, OrthonormalBasis.repr_apply_apply]
  rw [supportOrthonormalBasis, OrthonormalBasis.coe_mk]
  change 0 < inner ℝ (-unitDual l) x
  rw [inner_neg_left]
  simp only [unitDual, real_inner_smul_left, inner_dualVector]
  have hnorm : 0 < ‖dualVector l‖ := norm_pos_iff.mpr (dualVector_ne_zero hl)
  have hinv : 0 < ‖dualVector l‖⁻¹ := inv_pos.mpr hnorm
  nlinarith

end Erdos957StrictFrame
