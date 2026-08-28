import Wikipedia.HomotopyGroupsOfSpheres.CliffordSourceCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordCandidateGenerator
import Wikipedia.HomotopyGroupsOfSpheres.PointedCubeGenerators

/-!
# The degree-twelve candidate generates exactly when the corrected Clifford class does

Both target and parameter coordinate changes are actual based homeomorphisms.
Their action is checked on native cubes before transferring the generator
criterion. Primitivity of the corrected class is not assumed or asserted.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices

attribute [local irreducible] ComplexCliffordFive.stableCliffordInput
  ComplexCliffordFive.parameterHomeomorph rawCliffordSource targetCoordinateHomeomorph parameterCube

def reparametrizedParameterCube : GenLoop (Fin 5) ComplexCrossProductUnitary.UnitSphere axis :=
  pointedMapGenLoop
    (ComplexCliffordFive.parameterHomeomorph :
      C(ComplexCrossProductUnitary.UnitSphere, ComplexCrossProductUnitary.UnitSphere))
    axis axis ComplexCliffordFive.parameterHomeomorph_axis parameterCube

def reparametrizedParameterClass : π_ 5 ComplexCrossProductUnitary.UnitSphere axis :=
  ⟦reparametrizedParameterCube⟧

theorem reparametrizedParameterCube_generates :
    Function.Surjective (fun k : ℤ ↦ reparametrizedParameterClass ^ k) :=
  PointedCubeGenerators.homeomorph_cube_generates ComplexCliffordFive.parameterHomeomorph
    axis axis ComplexCliffordFive.parameterHomeomorph_axis parameterCube
    parameterCubeClass_generates

def normalizedInputClass : π_ 5 (Space (Fin 6 ⊕ Fin 6)) identity :=
  ⟦normalizedCliffordCube parameterCube⟧

def correctedInputClass : π_ 5 (Space (Fin 6 ⊕ Fin 6)) identity :=
  ⟦correctedCube parameterCube⟧

theorem normalizedInputClass_eq_correctedInputClass : normalizedInputClass = correctedInputClass :=
  normalizedCliffordClass_eq_corrected parameterCube

def targetCoordinatePiFiveMulEquiv :
    π_ 5 (Space (Fin (3 + 9))) identity ≃* π_ 5 (Space (Fin 6 ⊕ Fin 6)) identity :=
  pointedHomeomorphMulEquiv targetCoordinateHomeomorph identity identity
    targetCoordinateHomeomorph_identity

theorem targetCoordinatePiFiveMulEquiv_stable :
    targetCoordinatePiFiveMulEquiv ComplexCliffordFive.stableCliffordClass =
      (⟦normalizedCliffordCube reparametrizedParameterCube⟧ :
        π_ 5 (Space (Fin 6 ⊕ Fin 6)) identity) :=
  PointedCubeGenerators.homeomorph_comp_cube_class
    ComplexCliffordFive.stableCliffordInput rawCliffordSource targetCoordinateHomeomorph
    (ComplexCliffordFive.parameterHomeomorph :
      C(ComplexCrossProductUnitary.UnitSphere, ComplexCrossProductUnitary.UnitSphere))
    axis identity identity ComplexCliffordFive.stableCliffordInput_axis rawCliffordSource_axis
    targetCoordinateHomeomorph_identity ComplexCliffordFive.parameterHomeomorph_axis
    targetCoordinateHomeomorph_apply parameterCube

theorem stableClifford_generates_iff_normalized :
    Function.Surjective (fun k : ℤ ↦ ComplexCliffordFive.stableCliffordClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ normalizedInputClass ^ k) := by
  have he := CyclicGenerators.equiv_generates_iff targetCoordinatePiFiveMulEquiv
    ComplexCliffordFive.stableCliffordClass
  rw [targetCoordinatePiFiveMulEquiv_stable] at he
  exact he.symm.trans (PointedCubeGenerators.mapped_generators_iff rawCliffordSource axis identity
    rawCliffordSource_axis reparametrizedParameterCube parameterCube
      reparametrizedParameterCube_generates parameterCubeClass_generates)

theorem stableClifford_generates_iff_corrected :
    Function.Surjective (fun k : ℤ ↦ ComplexCliffordFive.stableCliffordClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ correctedInputClass ^ k) := by
  rw [stableClifford_generates_iff_normalized, normalizedInputClass_eq_correctedInputClass]

theorem sphereCandidate_generates_iff_corrected :
    Function.Surjective (fun k : ℤ ↦ sphereCandidateClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ correctedInputClass ^ k) :=
  ComplexCliffordFive.sphereCandidate_generates_iff_clifford.trans
    stableClifford_generates_iff_corrected

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
