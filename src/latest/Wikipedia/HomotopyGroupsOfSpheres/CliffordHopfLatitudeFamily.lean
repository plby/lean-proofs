import Wikipedia.HomotopyGroupsOfSpheres.CliffordAngularFourCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.CliffordHopfFrameLift

/-! # The actual Hopf latitude family factors through its lifted native cube -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.DegreeCollapse.SphereCube
open LatitudeDescent

def fourAngularParameterMap : C(I × EquatorSphere, UnitSphere) :=
  (basedAngularFourSphereHomeomorph : C(Sphere 4, UnitSphere)).comp
    ⟨fun p ↦ Latitude.point 3 p.1 p.2, by fun_prop⟩

theorem fourAngularParameterMap_apply (t : I) (q : EquatorSphere) :
    fourAngularParameterMap (t, q) =
      fourLatitudePoint ((t : ℝ) * Real.pi) (basedSphereThreeHomeomorph q) :=
  basedAngularFourSphereHomeomorph_point t q

def hopfLatitudeFamily : SingleFamily 3 (BalancedRealInvolutions.Space 6) (rawBalanced pole) where
  map := hopfCorrectedSphereMap.comp fourAngularParameterMap
  zero q := by
    change hopfCorrectedSphereMap (fourAngularParameterMap (0, q)) = rawBalanced pole
    rw [fourAngularParameterMap_apply]
    change hopfCorrectedSphereMap
      (fourLatitudePoint ((0 : ℝ) * Real.pi) (basedSphereThreeHomeomorph q)) = rawBalanced pole
    rw [zero_mul, fourLatitudePoint_zero, hopfCorrectedSphereMap_pole]
  one q := by
    change hopfCorrectedSphereMap (fourAngularParameterMap (1, q)) = rawBalanced pole
    rw [fourAngularParameterMap_apply]
    change hopfCorrectedSphereMap
      (fourLatitudePoint ((1 : ℝ) * Real.pi) (basedSphereThreeHomeomorph q)) = rawBalanced pole
    rw [one_mul, hopfCorrectedSphereMap_pi]

theorem hopfLatitudeFamily_parameter_point (t : I) :
    hopfLatitudeFamily.map (t, point 3) = rawBalanced pole := by
  change hopfCorrectedSphereMap (fourAngularParameterMap (t, point 3)) = rawBalanced pole
  rw [fourAngularParameterMap_apply, basedSphereThreeHomeomorph_point]
  exact hopfCorrectedSphereMap_reference _ (mul_nonneg t.property.1 Real.pi_pos.le)
    (by nlinarith [t.property.2, Real.pi_pos])

theorem hopfLatitudeFamily_sphereMap :
    hopfLatitudeFamily.toSphereMap = hopfCorrectedSphereMap.comp
      (basedAngularFourSphereHomeomorph : C(Sphere 4, UnitSphere)) := by
  apply ContinuousMap.ext
  intro w
  obtain ⟨⟨t, q⟩, rfl⟩ := Latitude.point_surjective 3 w
  rw [SingleFamily.toSphereMap_point]
  rfl

def hopfLatitudeInputClass : π_ 4 (BalancedRealInvolutions.Space 6) (rawBalanced pole) :=
  ⟦hopfLatitudeCube parameterThreeCube⟧

theorem hopfLatitudeFamily_nativeCube :
    SingleFamily.nativeCube hopfLatitudeFamily hopfLatitudeFamily_parameter_point =
      hopfLatitudeCube parameterThreeCube := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change hopfCorrectedSphereMap (fourAngularParameterMap (t 0, quotient 3 (Fin.tail t))) =
    hopfCorrectedSphereMap
      (fourLatitudePoint ((t 0 : ℝ) * Real.pi) (parameterThreeCube (Fin.tail t)))
  rw [fourAngularParameterMap_apply, parameterThreeCube_apply]

theorem hopfLatitudeFamily_nativeClass :
    SingleFamily.nativeClass hopfLatitudeFamily hopfLatitudeFamily_parameter_point =
      hopfLatitudeInputClass :=
  congrArg (fun p : GenLoop (Fin 4) (BalancedRealInvolutions.Space 6) (rawBalanced pole) ↦
    (⟦p⟧ : π_ 4 (BalancedRealInvolutions.Space 6) (rawBalanced pole))) hopfLatitudeFamily_nativeCube

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
