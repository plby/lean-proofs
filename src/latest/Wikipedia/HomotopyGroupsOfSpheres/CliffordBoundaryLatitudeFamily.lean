import Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryAngularCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryCorrection

/-! # The corrected endpoint's latitude cube is the actual orthogonal Bott image -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott

open CliffordFiveHermitian NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.DegreeCollapse.SphereCube LatitudeDescent

def angularParameterMap : C(I × Sphere 2, EquatorSphere) :=
  (basedAngularSphereHomeomorph : C(Sphere 3, EquatorSphere)).comp
    ⟨fun p ↦ Latitude.point 2 p.1 p.2, by fun_prop⟩

theorem angularParameterMap_apply (t : I) (v : Sphere 2) :
    angularParameterMap (t, v) = latitudePoint ((t : ℝ) * Real.pi) (parameterHomeomorph v) :=
  basedAngularSphereHomeomorph_point t v

def latitudeFamily : SingleFamily 2 (OrthogonalOperators 6) 1 where
  map := correctedMap.comp angularParameterMap
  zero v := by
    change correctedMap (angularParameterMap (0, v)) = 1
    rw [angularParameterMap_apply]
    change correctedMap (latitudePoint ((0 : ℝ) * Real.pi) (parameterHomeomorph v)) = 1
    rw [zero_mul, latitudePoint_zero, correctedMap_equatorPole]
  one v := by
    change correctedMap (angularParameterMap (1, v)) = 1
    rw [angularParameterMap_apply]
    change correctedMap (latitudePoint ((1 : ℝ) * Real.pi) (parameterHomeomorph v)) = 1
    rw [one_mul, correctedMap_pi]

theorem latitudeFamily_parameter_point (t : I) : latitudeFamily.map (t, point 2) = 1 := by
  change correctedMap (angularParameterMap (t, point 2)) = 1
  rw [angularParameterMap_apply, parameterHomeomorph_point]
  exact correctedMap_reference _ (mul_nonneg t.property.1 Real.pi_pos.le)
    (by nlinarith [t.property.2, Real.pi_pos])

theorem latitudeFamily_sphereMap : latitudeFamily.toSphereMap =
    correctedMap.comp (basedAngularSphereHomeomorph : C(Sphere 3, EquatorSphere)) := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨⟨t, v⟩, rfl⟩ := Latitude.point_surjective 2 q
  rw [SingleFamily.toSphereMap_point]
  rfl

def structureCube : GenLoop (Fin 2) (OrthogonalComplexStructures.Space 6)
    (structureMap structurePole) :=
  pointedMapGenLoop structureMap structurePole (structureMap structurePole) rfl parameterCube

def structureClass : π_ 2 (OrthogonalComplexStructures.Space 6) (structureMap structurePole) :=
  ⟦structureCube⟧

theorem latitudeFamily_nativeCube :
    SingleFamily.nativeCube latitudeFamily latitudeFamily_parameter_point =
      OrthogonalBottNative.nativeCube (structureMap structurePole) structureCube := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change correctedMap (angularParameterMap (t 0, quotient 2 (Fin.tail t))) =
    OrthogonalBottNative.nativeCube (structureMap structurePole) structureCube t
  rw [angularParameterMap_apply, ← parameterCube_apply, correctedMap_bott,
    OrthogonalBottNative.nativeCube_apply, OrthogonalBottNative.loopMap_apply]
  rfl

theorem latitudeFamily_nativeClass :
    SingleFamily.nativeClass latitudeFamily latitudeFamily_parameter_point =
      OrthogonalBottNative.degreeShift 2 (structureMap structurePole) (by decide)
        structureClass := by
  have h := congrArg (fun p : GenLoop (Fin 3) (OrthogonalOperators 6) 1 ↦
    (⟦p⟧ : π_ 3 (OrthogonalOperators 6) 1)) latitudeFamily_nativeCube
  exact h.trans (OrthogonalBottNative.degreeShift_mk 2 (structureMap structurePole)
    (by decide) structureCube).symm

end Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott
