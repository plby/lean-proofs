import Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordRankReduction
import Wikipedia.HomotopyGroupsOfSpheres.SphereCoordinateIsometries

/-!
# The reduced Clifford matrix is the actual cross-product matrix

Conjugating the first and third complex coordinates and multiplying by two
fixed real orthogonal matrices gives precisely the original polynomial map.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive

open ComplexCrossProductUnitary

def coordinateConjugation (z : Vector) : Vector := ![star (z 0), z 1, star (z 2)]

def parameterIsometry : EuclideanSpace ℂ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin 3) :=
  LinearIsometryEquiv.piLpCongrRight 2
    ![Complex.conjLIE, LinearIsometryEquiv.refl ℝ ℂ, Complex.conjLIE]

def parameterHomeomorph : UnitSphere ≃ₜ UnitSphere :=
  SphereCenteredCoordinates.sphereIsometry parameterIsometry

theorem parameterHomeomorph_val (z : UnitSphere) :
    (fun i ↦ (parameterHomeomorph z).val i) = coordinateConjugation z.val := by
  funext i
  fin_cases i <;> rfl

theorem parameterHomeomorph_axis : parameterHomeomorph axis = axis := by
  have hc : coordinateConjugation (fun i ↦ axis.val i) = (fun i ↦ axis.val i) := by
    rw [axis_val]
    simp [coordinateConjugation]
  apply Subtype.ext
  apply PiLp.ext
  intro i
  exact congrFun ((parameterHomeomorph_val axis).trans hc) i

def leftFactor : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

def rightFactor : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 0, 0, -1; 1, 0, 0]

theorem leftFactor_mul_transpose : leftFactor * leftFactor.transpose = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [leftFactor, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]

theorem rightFactor_mul_transpose : rightFactor * rightFactor.transpose = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rightFactor, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]

theorem reducedPolynomial_crossProduct (z : Vector) :
    leftFactor * reducedPolynomial (coordinateConjugation z) * rightFactor =
      ComplexCrossProductUnitary.matrix z := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [leftFactor, rightFactor, reducedPolynomial, coordinateConjugation,
      ComplexCrossProductUnitary.matrix, outer, crossMatrix,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two] <;> ring

theorem reduced_crossProduct (z : UnitSphere) :
    leftFactor * (reduced (parameterHomeomorph z)).val * rightFactor =
      (ComplexCrossProductUnitary.unitaryMap z).val := by
  rw [reduced_val, ComplexCrossProductUnitary.unitaryMap_val]
  change leftFactor * reducedPolynomial (fun i ↦ (parameterHomeomorph z).val i) *
    rightFactor = ComplexCrossProductUnitary.matrix z.val
  rw [parameterHomeomorph_val]
  exact reducedPolynomial_crossProduct z.val

theorem reduced_symmetric_crossProduct (z : UnitSphere) :
    (symmetricMap z).val.val =
      leftFactor * ((reduced (parameterHomeomorph z)).val *
        (reduced (parameterHomeomorph z)).val.transpose) * leftFactor.transpose := by
  rw [symmetricMap_val, ← ComplexCrossProductUnitary.unitaryMap_val, ← reduced_crossProduct]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc rightFactor, rightFactor_mul_transpose, Matrix.one_mul]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive
