import Wikipedia.HomotopyGroupsOfSpheres.LatitudeTimeHomeomorph
import Wikipedia.HomotopyGroupsOfSpheres.LatitudeHomeomorph
import Wikipedia.HomotopyGroupsOfSpheres.CliffordLatitudeCover
import Wikipedia.HomotopyGroupsOfSpheres.CliffordParameterFourCube
import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeFactorization

/-! # Based angular coordinates for the actual Clifford five-sphere -/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.DegreeCollapse.SphereCube
open LatitudeDescent

def angularSphereHomeomorph : Sphere 5 ≃ₜ ComplexCrossProductUnitary.UnitSphere :=
  (reversedTimeHomeomorph 4 angularTimeHomeomorph
    angularTimeHomeomorph_zero angularTimeHomeomorph_one).trans coordinateSphereHomeomorph

theorem angularSphereHomeomorph_point (t : I) (v : UnitSphere) :
    angularSphereHomeomorph (Latitude.point 4 t v) =
      latitudePoint ((t : ℝ) * Real.pi) v := by
  change coordinateSphereHomeomorph
    (reversedTimeHomeomorph 4 angularTimeHomeomorph
      angularTimeHomeomorph_zero angularTimeHomeomorph_one (Latitude.point 4 t v)) = _
  rw [reversedTimeHomeomorph_point, coordinateSphereHomeomorph_latitude,
    angularTimeHomeomorph_angle]

def basedAngularSphereHomeomorph : Sphere 5 ≃ₜ ComplexCrossProductUnitary.UnitSphere :=
  (latitudeHomeomorph 4 basedSphereFourHomeomorph).trans angularSphereHomeomorph

theorem basedAngularSphereHomeomorph_point (t : I) (v : UnitSphere) :
    basedAngularSphereHomeomorph (Latitude.point 4 t v) =
      latitudePoint ((t : ℝ) * Real.pi) (basedSphereFourHomeomorph v) := by
  change angularSphereHomeomorph
    (latitudeHomeomorph 4 basedSphereFourHomeomorph (Latitude.point 4 t v)) = _
  rw [latitudeHomeomorph_point, angularSphereHomeomorph_point]

theorem basedAngularSphereHomeomorph_basepoint :
    basedAngularSphereHomeomorph (SingleFamily.latitudeBasepoint 4) =
      ComplexCrossProductUnitary.axis := by
  rw [SingleFamily.latitudeBasepoint, basedAngularSphereHomeomorph_point]
  change latitudePoint ((0 : ℝ) * Real.pi) (basedSphereFourHomeomorph (point 4)) = _
  rw [zero_mul, latitudePoint_zero]

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
