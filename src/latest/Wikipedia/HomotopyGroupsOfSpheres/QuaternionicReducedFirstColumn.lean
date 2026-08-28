import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicReducedCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicReducedSevenCube

/-!
# The actual first column is an explicit quaternionic rational formula

This identifies the projection of the constructed native cube with its
coordinate formula. Its unit-column property follows from the proved
unitarity, rather than from an assumed degree or a numerical check.
-/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicSymmetricMatrices QuaternionicColumns QuaternionicRankOne

local notation "ℍ" => Quaternion ℝ

def firstColumnFormula (s t : ℝ) (B : Space (Fin 3)) (r : Fin 2) : ℍ :=
  let A := matrix (Real.cos s) (Real.sin s * Real.cos t) (Real.sin s * Real.sin t) B
  (A (remainingRow r) 1 - A (remainingRow r) 0 * (1 + A 1 0)⁻¹ * A 1 1) *
    star (-(scalarRotation s t * scalarRotation s t))

theorem reducedRotation_ratio_first_column (s t : ℝ) (B : Space (Fin 3)) (r : Fin 2) :
    (reducedRotation ((s, t), B) * (reducedRotation ((s, t), identity))⁻¹).val r 0 =
      firstColumnFormula s t B r := by
  change ((reducedRotation ((s, t), B)).val *
    star ((reducedRotation ((s, t), identity)).val)) r 0 = _
  rw [reducedRotation_identity_val]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
    star_zero, mul_zero, add_zero, Matrix.cons_val_zero]
  change (reduce (rotationInDomain ((s, t), B))).val r 0 *
    star (-(scalarRotation s t * scalarRotation s t)) = _
  rw [reduce_entry]
  rfl

theorem firstColumnFormula_pairing (s t : ℝ) (B : Space (Fin 3)) :
    pairing (firstColumnFormula s t B) (firstColumnFormula s t B) = 1 := by
  have he : (column 0
      (reducedRotation ((s, t), B) * (reducedRotation ((s, t), identity))⁻¹)).val =
        firstColumnFormula s t B :=
    funext (reducedRotation_ratio_first_column s t B)
  rw [← he]
  exact (column 0
    (reducedRotation ((s, t), B) * (reducedRotation ((s, t), identity))⁻¹)).property

theorem reducedTwoCubeMap_first_column (B : Space (Fin 3)) (u : Fin 2 → I) (r : Fin 2) :
    (reducedTwoCubeMap B u).val r 0 =
      firstColumnFormula ((u 0 : ℝ) * Real.pi) ((u 1 : ℝ) * Real.pi) B r := by
  rw [reducedTwoCubeMap_apply]
  exact reducedRotation_ratio_first_column _ _ B r

end QuaternionicBottMatrix

namespace ComplexCrossProductUnitary

theorem reducedSevenCubeSum_first_column (p : GenLoop (Fin 5) UnitSphere axis)
    (u : Fin 5 → I) (v : Fin 2 → I) (r : Fin 2) :
    (reducedSevenCubeSum p (Sum.elim u v)).val r 0 =
      QuaternionicBottMatrix.firstColumnFormula
        ((v 0 : ℝ) * Real.pi) ((v 1 : ℝ) * Real.pi) (symmetricMap (p u)) r := by
  rw [reducedSevenCubeSum_apply]
  exact QuaternionicBottMatrix.reducedTwoCubeMap_first_column _ _ _

end ComplexCrossProductUnitary
end Wikipedia.HomotopyGroupsOfSpheres
