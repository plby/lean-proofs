import Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordInputHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicParameterCube
import Wikipedia.HomotopyGroupsOfSpheres.PointedMapHomotopies

/-!
# The original stable input is homotopic to the explicit Clifford input

Every coordinate change and the complete homotopy are actual continuous maps.
The comparison fixes the parameter axis and survives all eight further matrix
stabilizations. Primitivity of the resulting Clifford class is not assumed.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices

attribute [local irreducible] crossProductHomotopy cliffordInput

def stableCliffordInput : C(UnitSphere, Space (Fin (3 + 9))) :=
  (stabilizationIterate 4 8).comp cliffordInput

theorem stableCliffordInput_axis : stableCliffordInput axis = identity := by
  change stabilizationIterate 4 8 (cliffordInput axis) = identity
  rw [cliffordInput_axis, stabilizationIterate_identity]

def stableCrossProductHomotopy :
    stableCliffordInput.HomotopyRel (stableSymmetricInput 9) {axis} :=
  (crossProductHomotopy.compContinuousMap (stabilizationIterate 4 8)).cast rfl
    (by
      apply ContinuousMap.ext
      intro z
      rfl)

attribute [local irreducible] stableCrossProductHomotopy stableCliffordInput
  stableSymmetricInput pointedMap

def stableCliffordCube : GenLoop (Fin 5) (Space (Fin (3 + 9))) identity :=
  pointedMapGenLoop stableCliffordInput axis identity stableCliffordInput_axis parameterCube

def stableCliffordClass : π_ 5 (Space (Fin (3 + 9))) identity := ⟦stableCliffordCube⟧

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive
