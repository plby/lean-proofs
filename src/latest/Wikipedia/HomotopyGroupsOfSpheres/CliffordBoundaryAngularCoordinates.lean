import Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryParameterCube
import Wikipedia.HomotopyGroupsOfSpheres.LatitudeHomeomorph
import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeFactorization

/-! # Based angular three-sphere coordinates for the actual boundary Bott family -/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott

open CliffordFiveHermitian Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.DegreeCollapse.SphereCube LatitudeDescent

def angularSphereHomeomorph : Sphere 3 ≃ₜ EquatorSphere :=
  reversedTimeHomeomorph 2 angularTimeHomeomorph
    angularTimeHomeomorph_zero angularTimeHomeomorph_one

theorem angularSphereHomeomorph_point (t : I) (v : Sphere 2) :
    angularSphereHomeomorph (Latitude.point 2 t v) = latitudePoint ((t : ℝ) * Real.pi) v := by
  change reversedTimeHomeomorph 2 angularTimeHomeomorph
    angularTimeHomeomorph_zero angularTimeHomeomorph_one (Latitude.point 2 t v) = _
  rw [reversedTimeHomeomorph_point, ← latitudePoint_arccos, angularTimeHomeomorph_angle]

def basedAngularSphereHomeomorph : Sphere 3 ≃ₜ EquatorSphere :=
  (latitudeHomeomorph 2 parameterHomeomorph).trans angularSphereHomeomorph

theorem basedAngularSphereHomeomorph_point (t : I) (v : Sphere 2) :
    basedAngularSphereHomeomorph (Latitude.point 2 t v) =
      latitudePoint ((t : ℝ) * Real.pi) (parameterHomeomorph v) := by
  change angularSphereHomeomorph
    (latitudeHomeomorph 2 parameterHomeomorph (Latitude.point 2 t v)) = _
  rw [latitudeHomeomorph_point, angularSphereHomeomorph_point]

theorem basedAngularSphereHomeomorph_basepoint :
    basedAngularSphereHomeomorph (SingleFamily.latitudeBasepoint 2) = equatorPole := by
  rw [SingleFamily.latitudeBasepoint, basedAngularSphereHomeomorph_point]
  change latitudePoint ((0 : ℝ) * Real.pi) (parameterHomeomorph (point 2)) = equatorPole
  rw [zero_mul, latitudePoint_zero]

end Wikipedia.HomotopyGroupsOfSpheres.CliffordBoundaryBott
