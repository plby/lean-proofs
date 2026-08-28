import Wikipedia.HomotopyGroupsOfSpheres.CliffordHopfLatitudeFamily
import Wikipedia.HomotopyGroupsOfSpheres.CliffordHopfCorrectedGenerator
import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeFourHomeomorphComparison

/-! # The candidate generates exactly when its explicit lifted Hopf latitude cube does -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open LatitudeDescent

attribute [local irreducible] hopfCorrectedSphereMap basedAngularFourSphereHomeomorph

theorem hopfCorrectedCube_class_eq_pointed (p : GenLoop (Fin 4) UnitSphere pole) :
    (⟦hopfCorrectedCube p⟧ : π_ 4 (BalancedRealInvolutions.Space 6) (rawBalanced pole)) =
      pointedMap hopfCorrectedSphereMap pole (rawBalanced pole) hopfCorrectedSphereMap_pole
        (⟦p⟧ : π_ 4 UnitSphere pole) :=
  (pointedMap_mk hopfCorrectedSphereMap pole (rawBalanced pole) hopfCorrectedSphereMap_pole p).symm

theorem hopfCorrectedInputClass_eq_pointed :
    hopfCorrectedInputClass =
      pointedMap hopfCorrectedSphereMap pole (rawBalanced pole) hopfCorrectedSphereMap_pole
        parameterFourClass := by
  have h₁ : hopfCorrectedInputClass = (⟦hopfCorrectedCube parameterFourCube⟧ :
      π_ 4 (BalancedRealInvolutions.Space 6) (rawBalanced pole)) := rfl
  have h₂ := hopfCorrectedCube_class_eq_pointed parameterFourCube
  have h₃ : (⟦parameterFourCube⟧ : π_ 4 UnitSphere pole) = parameterFourClass := rfl
  exact h₁.trans (h₂.trans (congrArg
    (pointedMap (N := Fin 4) hopfCorrectedSphereMap pole (rawBalanced pole)
      hopfCorrectedSphereMap_pole) h₃))

theorem hopfCorrected_generates_iff_latitude :
    Function.Surjective (fun k : ℤ ↦ hopfCorrectedInputClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ hopfLatitudeInputClass ^ k) := by
  rw [hopfCorrectedInputClass_eq_pointed]
  have h := SingleFamily.nativeFourCube_generates_iff_of_homeomorph
    hopfLatitudeFamily hopfLatitudeFamily_parameter_point
    basedAngularFourSphereHomeomorph pole basedAngularFourSphereHomeomorph_basepoint
    hopfCorrectedSphereMap hopfCorrectedSphereMap_pole hopfLatitudeFamily_sphereMap
    parameterFourClass parameterFourClass_generates
  rw [hopfLatitudeFamily_nativeClass] at h
  exact h

theorem sphereCandidate_generates_iff_hopfLatitude :
    Function.Surjective (fun k : ℤ ↦ ComplexCrossProductUnitary.sphereCandidateClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ hopfLatitudeInputClass ^ k) :=
  sphereCandidate_generates_iff_hopfCorrected.trans hopfCorrected_generates_iff_latitude

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
