import Wikipedia.HomotopyGroupsOfSpheres.SymmetricTraceZeroThreeCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductSignAction

/-!
# Sign conjugation preserves the five-dimensional symmetric-model orientation

The two diagonal coordinates are fixed. The three off-diagonal coordinates
acquire the three pairwise products of the coordinate signs; their product
is one. The resulting linear map is proved equal to actual matrix conjugation.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.RealSymmetricMixing

open ComplexCrossProductUnitary

def realSigns (x y : Bool) (r : Fin 3) : ℝ := (signs x y r).re

def threeSignWeights (x y : Bool) : Fin 5 → ℝ :=
  ![1, 1, realSigns x y 0 * realSigns x y 1,
    realSigns x y 0 * realSigns x y 2, realSigns x y 1 * realSigns x y 2]

def threeSignCoordinates (x y : Bool) : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) :=
  LinearMap.pi (fun r ↦ (threeSignWeights x y r • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp
    (LinearMap.proj r))

theorem threeSignCoordinates_apply (x y : Bool) (v : Fin 5 → ℝ) (r : Fin 5) :
    threeSignCoordinates x y v r = threeSignWeights x y r * v r := rfl

theorem threeSignCoordinates_det (x y : Bool) : (threeSignCoordinates x y).det = 1 := by
  rw [threeSignCoordinates, LinearMap.det_pi]
  simp only [LinearMap.det_smul, Module.finrank_self, pow_one, LinearMap.det_id, mul_one]
  cases x <;> cases y <;> norm_num [threeSignWeights, realSigns, signs, boolSign,
    Matrix.cons_val_two, Fin.prod_univ_succ]

def threeSignDirection (x y : Bool) : DirectionSpace (Fin 3) →ₗ[ℝ] DirectionSpace (Fin 3) :=
  threeDirectionEquiv.toLinearMap.comp
    ((threeSignCoordinates x y).comp threeDirectionEquiv.symm.toLinearMap)

theorem threeSignDirection_det (x y : Bool) : (threeSignDirection x y).det = 1 := by
  rw [threeSignDirection, LinearMap.det_conj]
  exact threeSignCoordinates_det x y

theorem threeSignDirection_val (x y : Bool) (A : DirectionSpace (Fin 3)) :
    (threeSignDirection x y A).val =
      Matrix.diagonal (realSigns x y) * A.val * Matrix.diagonal (realSigns x y) := by
  have hA := congrArg Subtype.val (threeDirection_coordinates A)
  change threeMatrix (threeCoordinates A) = A.val at hA
  change threeMatrix (threeSignCoordinates x y (threeCoordinates A)) = _
  rw [← hA]
  ext r s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases r <;> fin_cases s <;> cases x <;> cases y <;>
    simp [threeMatrix, threeSignCoordinates_apply, threeSignWeights, realSigns,
      signs, boolSign, Matrix.cons_val_two, sub_eq_add_neg]

end Wikipedia.HomotopyGroupsOfSpheres.RealSymmetricMixing
