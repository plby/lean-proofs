import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryStabilization
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicReducedCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicDoubleBottCube
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicStabilizationIterate

/-!
# The explicit based Bott matrices commute with actual stabilization

The new diagonal block in the raw rotation is the scalar reference rotation.
It cancels after reference division, leaving exactly the original bordered
quaternionic inclusion. The equality also holds for every iterate.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicColumns QuaternionicSymmetricMatrices MatrixBorder

local notation "ℍ" => Quaternion ℝ

variable {n : ℕ}

def scalarRotationUnit (s t : ℝ) : unitary ℍ :=
  ⟨scalarRotation s t, scalarRotation_unitary s t⟩

theorem rotation_stabilization (s t : ℝ) (B : Space (Fin n)) :
    rotation s t (QuaternionicSymmetricMatrices.stabilization n B) =
      unitaryBorder (scalarRotationUnit s t, rotation s t B) := by
  apply Subtype.ext
  apply Matrix.ext
  intro r q
  cases r using Fin.cases <;> cases q using Fin.cases <;>
    simp [rotation_val, matrix_apply, QuaternionicSymmetricMatrices.stabilization_val,
      unitaryBorder, border, scalarRotationUnit, scalarRotation, QuaternionicComplexPlane.embed,
      eq_comm]

theorem unitaryBorder_one (A : SpGroup (Fin n)) :
    unitaryBorder ((1 : unitary ℍ), A) = QuaternionicColumns.stabilization n A := rfl

attribute [local irreducible] rotation

theorem basedRotation_stabilization (s t : ℝ) (B : Space (Fin n)) :
    basedRotation s t (QuaternionicSymmetricMatrices.stabilization n B) =
      QuaternionicColumns.stabilization n (basedRotation s t B) := by
  have hi := QuaternionicSymmetricMatrices.stabilization_identity n
  change rotation s t (QuaternionicSymmetricMatrices.stabilization n B) *
    (rotation s t identity)⁻¹ = _
  rw [← hi, rotation_stabilization, rotation_stabilization, ← map_inv, ← map_mul]
  change unitaryBorder
    (scalarRotationUnit s t * (scalarRotationUnit s t)⁻¹,
      rotation s t B * (rotation s t identity)⁻¹) = _
  rw [mul_inv_cancel, unitaryBorder_one]
  rfl

theorem basedRotation_stabilizationIterate (s t : ℝ) (B : Space (Fin n)) (r : ℕ) :
    basedRotation s t (QuaternionicSymmetricMatrices.stabilizationIterate n r B) =
      QuaternionicColumns.stabilizationIterate n r (basedRotation s t B) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change basedRotation s t (QuaternionicSymmetricMatrices.stabilization (n + r)
      (QuaternionicSymmetricMatrices.stabilizationIterate n r B)) =
        QuaternionicColumns.stabilization (n + r)
          (QuaternionicColumns.stabilizationIterate n r (basedRotation s t B))
    rw [basedRotation_stabilization, ih]

theorem twoCubeMap_stabilizationIterate (B : Space (Fin n)) (r : ℕ) (u : Fin 2 → I) :
    twoCubeMap (QuaternionicSymmetricMatrices.stabilizationIterate n r B) u =
      QuaternionicColumns.stabilizationIterate n r (twoCubeMap B u) :=
  basedRotation_stabilizationIterate ((u 0 : ℝ) * Real.pi) ((u 1 : ℝ) * Real.pi) B r

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
