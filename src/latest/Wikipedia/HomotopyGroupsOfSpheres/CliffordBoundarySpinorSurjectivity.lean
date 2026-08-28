import Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundarySpinorLift
import Wikipedia.HomotopyGroupsOfSpheres.HomotopySurjectivity
import Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryGenerator
import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorConnectingEvaluation
import Wikipedia.HomotopyGroupsOfSpheres.SpinorSphereTwoSurjectivity

/-!
# The explicit two-sphere surjects on the spinor homotopy group and the candidate is primitive
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott

open NoExoticSixSphere NoExoticSixSphere.CubeFirstCoordinate
open NoExoticSixSphere.RankSixComplexProjection

theorem structureMap_surjective_rebased :
    Function.Surjective (pointedMap (N := Fin 2) structureMap structurePole
      (fromSpinor poleSpinor) structureMap_pole) :=
  spinorSphereTwo_pointed_surjective poleSpinor structureMap structurePole structureMap_pole
    exists_connecting_sphere

theorem structureMap_surjective :
    Function.Surjective (pointedMap (N := Fin 2) structureMap structurePole
      (structureMap structurePole) rfl) :=
  (pointedMap_surjective_iff_rebase structureMap structurePole
    (fromSpinor poleSpinor) structureMap_pole).mp structureMap_surjective_rebased

theorem structureClass_generates :
    Function.Surjective (fun k : ℤ ↦ structureClass ^ k) := by
  have h : pointedMap structureMap structurePole (structureMap structurePole) rfl parameterClass =
      structureClass :=
    pointedMap_mk structureMap structurePole (structureMap structurePole) rfl parameterCube
  rw [← h]
  exact (CyclicGenerators.map_generates_iff
    (pointedMap structureMap structurePole (structureMap structurePole) rfl)
    parameterClass parameterClass_generates).mpr structureMap_surjective

theorem sphereCandidate_generates :
    Function.Surjective (fun k : ℤ ↦ ComplexCrossProductUnitary.sphereCandidateClass ^ k) :=
  sphereCandidate_generates_iff_structure.mpr structureClass_generates

end Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott
