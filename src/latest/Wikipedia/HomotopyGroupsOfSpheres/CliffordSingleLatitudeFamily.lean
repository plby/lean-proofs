import Wikipedia.HomotopyGroupsOfSpheres.CliffordAngularCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.CliffordBottHomotopy

/-! # The corrected Clifford sphere family is the actual balanced Bott cube -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.DegreeCollapse.SphereCube
open QuaternionicSymmetricMatrices LatitudeDescent

theorem forgetSpecial_identity : forgetSpecial specialIdentity = identity := rfl

theorem correctedSphereMap_pi (v : UnitSphere) :
    correctedSphereMap (latitudePoint Real.pi v) = specialIdentity := by
  rw [correctedSphereMap_latitude Real.pi v Real.pi_pos.le le_rfl,
    BalancedRealInvolutions.rotation_pi, BalancedRealInvolutions.antipode,
    BalancedRealInvolutions.referenceAction_diagonal,
    show 2 * (-Real.pi / 2) + Real.pi = 0 by ring,
    BalancedRealInvolutions.diagonalSpecial_zero]

def angularParameterMap : C(I × UnitSphere, ComplexCrossProductUnitary.UnitSphere) :=
  (basedAngularSphereHomeomorph : C(Sphere 5, ComplexCrossProductUnitary.UnitSphere)).comp
    ⟨fun p ↦ Latitude.point 4 p.1 p.2, by fun_prop⟩

theorem angularParameterMap_apply (t : I) (v : UnitSphere) :
    angularParameterMap (t, v) =
      latitudePoint ((t : ℝ) * Real.pi) (basedSphereFourHomeomorph v) :=
  basedAngularSphereHomeomorph_point t v

def correctedLatitudeFamily : SingleFamily 4 (Space (Fin 6 ⊕ Fin 6)) identity where
  map := correctedUnderlyingMap.comp angularParameterMap
  zero v := by
    change correctedUnderlyingMap (angularParameterMap (0, v)) = identity
    rw [angularParameterMap_apply]
    change correctedUnderlyingMap
      (latitudePoint ((0 : ℝ) * Real.pi) (basedSphereFourHomeomorph v)) = identity
    rw [zero_mul, latitudePoint_zero, correctedUnderlyingMap_axis]
  one v := by
    change correctedUnderlyingMap (angularParameterMap (1, v)) = identity
    rw [angularParameterMap_apply]
    change (correctedSphereMap
      (latitudePoint ((1 : ℝ) * Real.pi) (basedSphereFourHomeomorph v))).val = identity
    rw [one_mul, correctedSphereMap_pi]
    rfl

theorem correctedLatitudeFamily_parameter_point (t : I) :
    correctedLatitudeFamily.map (t, point 4) = identity := by
  change correctedUnderlyingMap (angularParameterMap (t, point 4)) = identity
  rw [angularParameterMap_apply, basedSphereFourHomeomorph_point]
  exact congrArg Subtype.val (correctedSphereMap_reference ((t : ℝ) * Real.pi)
    (mul_nonneg t.property.1 Real.pi_pos.le) (by nlinarith [t.property.2, Real.pi_pos]))

theorem correctedLatitudeFamily_sphereMap :
    correctedLatitudeFamily.toSphereMap = correctedUnderlyingMap.comp
      (basedAngularSphereHomeomorph : C(Sphere 5, ComplexCrossProductUnitary.UnitSphere)) := by
  apply ContinuousMap.ext
  intro w
  obtain ⟨⟨t, v⟩, rfl⟩ := Latitude.point_surjective 4 w
  rw [SingleFamily.toSphereMap_point]
  rfl

def balancedInputCube :
    GenLoop (Fin 4) (BalancedRealInvolutions.Space 6) (BalancedRealInvolutions.standard 6) :=
  balancedCube parameterFourCube

def balancedInputClass :
    π_ 4 (BalancedRealInvolutions.Space 6) (BalancedRealInvolutions.standard 6) :=
  ⟦balancedInputCube⟧

def balancedBottClass : π_ 5 (SpecialSpace (Fin 6 ⊕ Fin 6)) specialIdentity :=
  ⟦BalancedRealInvolutions.inducedCube 6 balancedInputCube⟧

def includedBalancedBottClass : π_ 5 (Space (Fin 6 ⊕ Fin 6)) identity :=
  pointedMap forgetSpecial specialIdentity identity forgetSpecial_identity balancedBottClass

theorem correctedLatitudeFamily_nativeCube :
    SingleFamily.nativeCube correctedLatitudeFamily correctedLatitudeFamily_parameter_point =
      pointedMapGenLoop forgetSpecial specialIdentity identity forgetSpecial_identity
        (BalancedRealInvolutions.inducedCube 6 balancedInputCube) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change correctedUnderlyingMap (angularParameterMap (t 0, quotient 4 (Fin.tail t))) =
    (BalancedRealInvolutions.inducedCube 6 balancedInputCube t).val
  rw [angularParameterMap_apply, ← parameterFourCube_apply]
  exact congrArg Subtype.val (correctedSphereMap_cube parameterFourCube t)

theorem correctedLatitudeFamily_nativeClass :
    SingleFamily.nativeClass correctedLatitudeFamily correctedLatitudeFamily_parameter_point =
      includedBalancedBottClass := by
  change (⟦SingleFamily.nativeCube correctedLatitudeFamily
    correctedLatitudeFamily_parameter_point⟧ : π_ 5 (Space (Fin 6 ⊕ Fin 6)) identity) =
      pointedMap forgetSpecial specialIdentity identity forgetSpecial_identity
        (⟦BalancedRealInvolutions.inducedCube 6 balancedInputCube⟧ :
          π_ 5 (SpecialSpace (Fin 6 ⊕ Fin 6)) specialIdentity)
  rw [pointedMap_mk, correctedLatitudeFamily_nativeCube]

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
