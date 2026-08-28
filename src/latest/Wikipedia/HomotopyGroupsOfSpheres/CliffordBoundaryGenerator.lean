import Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryLatitudeFamily
import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeThreeHomeomorphComparison

/-! # The original degree-twelve candidate reduces to the explicit complex-structure sphere -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott

open CliffordFiveHermitian NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

def correctedInputClass : π_ 3 (OrthogonalOperators 6) 1 :=
  ⟦correctedCube parameterThreeCube⟧

theorem boundaryInputClass_eq_corrected : boundaryInputClass = correctedInputClass :=
  boundaryClass_eq_corrected parameterThreeCube

theorem correctedCube_class_eq_pointed (p : GenLoop (Fin 3) EquatorSphere equatorPole) :
    (⟦correctedCube p⟧ : π_ 3 (OrthogonalOperators 6) 1) =
      pointedMap correctedMap equatorPole 1 correctedMap_equatorPole
        (⟦p⟧ : π_ 3 EquatorSphere equatorPole) :=
  (pointedMap_mk correctedMap equatorPole 1 correctedMap_equatorPole p).symm

theorem correctedInputClass_eq_pointed : correctedInputClass =
    pointedMap correctedMap equatorPole 1 correctedMap_equatorPole parameterThreeClass := by
  have h₁ : correctedInputClass =
      (⟦correctedCube parameterThreeCube⟧ : π_ 3 (OrthogonalOperators 6) 1) := rfl
  have h₂ := correctedCube_class_eq_pointed parameterThreeCube
  have h₃ : (⟦parameterThreeCube⟧ : π_ 3 EquatorSphere equatorPole) = parameterThreeClass := rfl
  exact h₁.trans (h₂.trans (congrArg
    (pointedMap (N := Fin 3) correctedMap equatorPole 1 correctedMap_equatorPole) h₃))

theorem corrected_generates_iff_structure :
    Function.Surjective (fun k : ℤ ↦ correctedInputClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ structureClass ^ k) := by
  rw [correctedInputClass_eq_pointed]
  have h := LatitudeDescent.SingleFamily.nativeThreeCube_generates_iff_of_homeomorph
    latitudeFamily latitudeFamily_parameter_point basedAngularSphereHomeomorph equatorPole
    basedAngularSphereHomeomorph_basepoint correctedMap correctedMap_equatorPole
    latitudeFamily_sphereMap parameterThreeClass parameterThreeClass_generates
  rw [latitudeFamily_nativeClass] at h
  exact h.trans (CyclicGenerators.equiv_generates_iff
    (OrthogonalBottNative.degreeShift 2 (structureMap structurePole) (by decide)) structureClass)

theorem sphereCandidate_generates_iff_structure :
    Function.Surjective (fun k : ℤ ↦ ComplexCrossProductUnitary.sphereCandidateClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ structureClass ^ k) := by
  rw [sphereCandidate_generates_iff_boundary, boundaryInputClass_eq_corrected]
  exact corrected_generates_iff_structure

end Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott
