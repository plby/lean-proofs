import Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordSymmetricCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.PointedHomotopyPrecomposition

/-! # The based homotopy from the Clifford input to the once-stabilized cross-product input -/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices

attribute [local irreducible] symmetricReductionHomotopy blockSymmetricClifford
  blockSymmetricReduced parameterHomeomorph

def reparametrizedReductionHomotopy :
    (blockSymmetricClifford.comp (parameterHomeomorph : C(_, _))).HomotopyRel
      (blockSymmetricReduced.comp (parameterHomeomorph : C(_, _))) {axis} :=
  pointedHomotopyPrecomp (f := blockSymmetricClifford) (g := blockSymmetricReduced)
    (y := axis) symmetricReductionHomotopy (parameterHomeomorph : C(UnitSphere, UnitSphere))
      axis parameterHomeomorph_axis

def cliffordInput : C(UnitSphere, Space (Fin 4)) :=
  outputTransform.comp (blockSymmetricClifford.comp (parameterHomeomorph : C(_, _)))

theorem cliffordInput_axis : cliffordInput axis = identity := by
  change outputTransform (blockSymmetricClifford (parameterHomeomorph axis)) = identity
  rw [parameterHomeomorph_axis, blockSymmetricClifford_axis, outputTransform_identity]

def crossProductHomotopy :
    cliffordInput.HomotopyRel ((stabilization 3).comp symmetricMap) {axis} :=
  (reparametrizedReductionHomotopy.compContinuousMap outputTransform).cast rfl
    (by
      apply ContinuousMap.ext
      intro z
      exact outputTransform_reduced z)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive
