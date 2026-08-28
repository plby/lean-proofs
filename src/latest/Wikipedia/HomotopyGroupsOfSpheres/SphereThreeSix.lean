import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicDegreeTwelve
import Wikipedia.HomotopyGroupsOfSpheres.SphereCoordinateIsometries
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The sixth homotopy group of the literal three-sphere is cyclic of order twelve

The isomorphism uses the actual quaternionic exact sequence, the proved
degree-twelve generator, and an explicit isometry changing the sphere base point.
No generator, order, degree, connectivity, or exactness assumption remains.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

def sphereThreeBasepointHomeomorph (x y : Sphere 3) : Sphere 3 ≃ₜ Sphere 3 :=
  SphereCenteredCoordinates.sphereIsometry ((ℝ ∙ (x.val - y.val))ᗮ.reflection)

theorem sphereThreeBasepointHomeomorph_apply (x y : Sphere 3) :
    sphereThreeBasepointHomeomorph x y x = y := by
  apply Subtype.ext
  apply Submodule.reflection_sub
  rw [mem_sphere_zero_iff_norm.mp x.property, mem_sphere_zero_iff_norm.mp y.property]

/-- Unconditionally, the native sixth homotopy group of `S³` is `ℤ/12ℤ`. -/
def pi6_sphere_three_mulEquiv (x : Sphere 3) :
    π_ 6 (Sphere 3) x ≃* Multiplicative (ZMod 12) :=
  (pointedHomeomorphMulEquiv (N := Fin 6)
    (sphereThreeBasepointHomeomorph x (QuaternionicFibration.fiberSphereHomeomorph 1))
    x (QuaternionicFibration.fiberSphereHomeomorph 1)
    (sphereThreeBasepointHomeomorph_apply x (QuaternionicFibration.fiberSphereHomeomorph 1))).trans
      QuaternionicFibration.piSixBaseMulEquiv

end Wikipedia.HomotopyGroupsOfSpheres
