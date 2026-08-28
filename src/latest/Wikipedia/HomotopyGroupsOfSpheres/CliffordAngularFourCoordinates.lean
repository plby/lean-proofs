import Wikipedia.HomotopyGroupsOfSpheres.CliffordFourLatitude
import Wikipedia.HomotopyGroupsOfSpheres.CliffordParameterThreeCube
import Wikipedia.HomotopyGroupsOfSpheres.LatitudeHomeomorph
import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeFactorization

/-! # Based angular coordinates for the actual Clifford four-sphere -/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.DegreeCollapse.SphereCube
open LatitudeDescent

def angularFourSphereHomeomorph : Sphere 4 ≃ₜ UnitSphere :=
  reversedTimeHomeomorph 3 angularTimeHomeomorph
    angularTimeHomeomorph_zero angularTimeHomeomorph_one

theorem angularFourSphereHomeomorph_point (t : I) (q : EquatorSphere) :
    angularFourSphereHomeomorph (Latitude.point 3 t q) =
      fourLatitudePoint ((t : ℝ) * Real.pi) q := by
  change reversedTimeHomeomorph 3 angularTimeHomeomorph
    angularTimeHomeomorph_zero angularTimeHomeomorph_one (Latitude.point 3 t q) = _
  rw [reversedTimeHomeomorph_point, ← fourLatitudePoint_arccos, angularTimeHomeomorph_angle]

def basedAngularFourSphereHomeomorph : Sphere 4 ≃ₜ UnitSphere :=
  (latitudeHomeomorph 3 basedSphereThreeHomeomorph).trans angularFourSphereHomeomorph

theorem basedAngularFourSphereHomeomorph_point (t : I) (q : EquatorSphere) :
    basedAngularFourSphereHomeomorph (Latitude.point 3 t q) =
      fourLatitudePoint ((t : ℝ) * Real.pi) (basedSphereThreeHomeomorph q) := by
  change angularFourSphereHomeomorph
    (latitudeHomeomorph 3 basedSphereThreeHomeomorph (Latitude.point 3 t q)) = _
  rw [latitudeHomeomorph_point, angularFourSphereHomeomorph_point]

theorem basedAngularFourSphereHomeomorph_basepoint :
    basedAngularFourSphereHomeomorph (SingleFamily.latitudeBasepoint 3) = pole := by
  rw [SingleFamily.latitudeBasepoint, basedAngularFourSphereHomeomorph_point]
  change fourLatitudePoint ((0 : ℝ) * Real.pi) (basedSphereThreeHomeomorph (point 3)) = pole
  rw [zero_mul, fourLatitudePoint_zero]

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
