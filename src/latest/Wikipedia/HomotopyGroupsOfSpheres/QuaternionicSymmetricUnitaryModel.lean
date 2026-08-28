import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrixAlgebra
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicJointAntipodalDiagonalization
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicAnticommutingStructures

/-!
# The symmetric unitary model for the second Bott parameter space

The inverse maps use actual quaternionic coefficients, with entries `z j`.
Both are continuous in the existing subspace topologies. The standard
anticommuting structure corresponds to the identity complex matrix.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.AnticommutingStructures

open QuaternionicSymmetricMatrices

local notation "ℍ" => Quaternion ℝ

variable {n : ℕ}

def symmetricCoordinates (P : Space (ComplexStructures.standard n)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  complexMatrix (coefficients n P.val.val.val)

theorem quaternionMatrix_symmetricCoordinates (P : Space (ComplexStructures.standard n)) :
    quaternionMatrix (symmetricCoordinates P) = coefficients n P.val.val.val := by
  apply quaternionMatrix_complexMatrix
  have h := coefficients_anticommute (ComplexStructures.standard n) P.val.val P.property
  have hs : coefficients n (ComplexStructures.standard n).val.val =
      ComplexStructures.standardMatrix n := coefficients_realAction n _
  rw [hs] at h
  exact h

theorem symmetricCoordinates_transpose (P : Space (ComplexStructures.standard n)) :
    (symmetricCoordinates P).transpose = symmetricCoordinates P := by
  apply (quaternionMatrix_skew_iff _).mp
  rw [quaternionMatrix_symmetricCoordinates]
  exact coefficients_skew P.val.val

theorem symmetricCoordinates_unitary (P : Space (ComplexStructures.standard n)) :
    symmetricCoordinates P ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  apply (quaternionMatrix_square_iff _ (symmetricCoordinates_transpose P)).mp
  rw [quaternionMatrix_symmetricCoordinates]
  exact coefficients_complexStructure_square P.val

def toSymmetricUnitary (P : Space (ComplexStructures.standard n)) :
    QuaternionicSymmetricMatrices.Space (Fin (n + 1)) :=
  ⟨⟨symmetricCoordinates P, symmetricCoordinates_unitary P⟩, symmetricCoordinates_transpose P⟩

def ofSymmetricUnitary (B : QuaternionicSymmetricMatrices.Space (Fin (n + 1))) :
    Space (ComplexStructures.standard n) :=
  ⟨complexStructureOfMatrix n (quaternionMatrix B.val.val)
      ((quaternionMatrix_skew_iff _).mpr B.property)
      ((quaternionMatrix_square_iff _ B.property).mpr B.val.property), by
    change realRepresentation n (ComplexStructures.standardMatrix n) *
        realRepresentation n (quaternionMatrix B.val.val) =
      -(realRepresentation n (quaternionMatrix B.val.val) *
        realRepresentation n (ComplexStructures.standardMatrix n))
    rw [← map_mul, ← map_mul, ← map_neg]
    exact congrArg (realRepresentation n) (quaternionMatrix_anticommutes B.val.val)⟩

theorem ofSymmetricUnitary_toSymmetricUnitary (P : Space (ComplexStructures.standard n)) :
    ofSymmetricUnitary (toSymmetricUnitary P) = P := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change realAction n (quaternionMatrix (symmetricCoordinates P)) = P.val.val.val
  rw [quaternionMatrix_symmetricCoordinates]
  exact realAction_coefficients n P.val.val.val P.val.val.property.2

theorem toSymmetricUnitary_ofSymmetricUnitary
    (B : QuaternionicSymmetricMatrices.Space (Fin (n + 1))) :
    toSymmetricUnitary (ofSymmetricUnitary B) = B := by
  apply Subtype.ext
  apply Subtype.ext
  change complexMatrix (coefficients n (realAction n (quaternionMatrix B.val.val))) = B.val.val
  rw [coefficients_realAction, complexMatrix_quaternionMatrix]

theorem continuous_toSymmetricUnitary :
    Continuous (toSymmetricUnitary (n := n)) := by
  have hv : Continuous (fun P : Space (ComplexStructures.standard n) ↦ P.val.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hc : Continuous (fun P : Space (ComplexStructures.standard n) ↦ symmetricCoordinates P) :=
    continuous_complexMatrix.comp ((continuous_coefficients n).comp hv)
  exact (hc.subtype_mk _).subtype_mk _

theorem continuous_ofSymmetricUnitary :
    Continuous (ofSymmetricUnitary (n := n)) := by
  have hv : Continuous (fun B : QuaternionicSymmetricMatrices.Space (Fin (n + 1)) ↦ B.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hr : Continuous (fun B : QuaternionicSymmetricMatrices.Space (Fin (n + 1)) ↦
      realAction n (quaternionMatrix B.val.val)) :=
    (continuous_realAction n).comp (continuous_quaternionMatrix.comp hv)
  exact ((hr.subtype_mk _).subtype_mk _).subtype_mk _

/-- The actual homeomorphism, not an abstract equivalence of underlying sets. -/
def symmetricUnitaryHomeomorph (n : ℕ) :
    Space (ComplexStructures.standard n) ≃ₜ QuaternionicSymmetricMatrices.Space (Fin (n + 1)) where
  toFun := toSymmetricUnitary
  invFun := ofSymmetricUnitary
  left_inv := ofSymmetricUnitary_toSymmetricUnitary
  right_inv := toSymmetricUnitary_ofSymmetricUnitary
  continuous_toFun := continuous_toSymmetricUnitary
  continuous_invFun := continuous_ofSymmetricUnitary

theorem ofSymmetricUnitary_identity (n : ℕ) :
    ofSymmetricUnitary (identity : QuaternionicSymmetricMatrices.Space (Fin (n + 1))) =
      standard n := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change realAction n (quaternionMatrix (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) =
    realAction n (jMatrix n)
  rw [quaternionMatrix_identity]
  rfl

theorem symmetricUnitaryHomeomorph_standard (n : ℕ) :
    symmetricUnitaryHomeomorph n (standard n) = identity := by
  rw [← ofSymmetricUnitary_identity n]
  exact toSymmetricUnitary_ofSymmetricUnitary _

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.AnticommutingStructures
