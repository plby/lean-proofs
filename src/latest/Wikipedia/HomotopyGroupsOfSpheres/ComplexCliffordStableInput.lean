import Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordStableHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.PointedHomotopyClassComparison

/-! # Equality of the actual stable Clifford and cross-product native classes -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices

attribute [local irreducible] stableCrossProductHomotopy stableCliffordInput
  stableSymmetricInput

theorem stableCliffordClass_eq_stableInput : stableCliffordClass = stableInputClass 9 :=
  Quotient.sound (pointedMapGenLoop_homotopic_of_homotopyRel (N := Fin 5)
    stableCliffordInput (stableSymmetricInput 9) axis identity
    stableCliffordInput_axis (stableSymmetricInput_axis 9) stableCrossProductHomotopy parameterCube)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive
