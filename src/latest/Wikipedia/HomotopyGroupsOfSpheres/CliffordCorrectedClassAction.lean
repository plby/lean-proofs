import Wikipedia.HomotopyGroupsOfSpheres.CliffordBottHomotopy

/-! # The actual native class action of the corrected Clifford map -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices

attribute [local irreducible] correctedUnderlyingMap

theorem correctedCube_class_eq_pointed
    (p : GenLoop (Fin 5) ComplexCrossProductUnitary.UnitSphere axis) :
    (⟦correctedCube p⟧ : π_ 5 (Space (Fin 6 ⊕ Fin 6)) identity) =
      pointedMap correctedUnderlyingMap axis identity correctedUnderlyingMap_axis
        (⟦p⟧ : π_ 5 ComplexCrossProductUnitary.UnitSphere axis) :=
  (pointedMap_mk correctedUnderlyingMap axis identity correctedUnderlyingMap_axis p).symm

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
