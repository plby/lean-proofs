import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicConnectingHom
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBaseExactness

/-!
# The proved exact homotopy sequence of the quaternionic fibration

This supplies the segment

`π₇(Sp(2)) → π₇(S⁷) → π₆(S³) → π₆(Sp(2))`

on the original native homotopy groups, with explicit homeomorphisms
identifying the base and fiber with the standard Euclidean spheres.
The computations of the groups of `Sp(2)` and the index of the projection's
image are not assumed and are not supplied by this file.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

variable (n : ℕ) [NeZero n]

theorem projection_range_eq_connecting_ker :
    (projectionMap n).range = (connectingHom n).ker := by
  ext a
  exact projectionMap_range_eq_connecting_kernel a

theorem connecting_range_eq_inclusion_ker :
    (connectingHom n).range = (inclusionMap n).ker := by
  ext a
  exact connecting_range_eq_kernel a

/-- The actual stabilizer subgroup identified with the literal three-sphere. -/
def fiberSphereHomeomorph : northSubgroup ≃ₜ Sphere 3 :=
  northFiberHomeomorph.symm.trans HopfProblem.UnitQuaternionSphere.sphereHomeomorph

/-- The connecting homomorphism written using the standard Euclidean sphere types. -/
def sphereConnectingHom :
    π_ (n + 1) (Sphere 7) (baseSphereHomeomorph north) →*
      π_ n (Sphere 3) (fiberSphereHomeomorph 1) :=
  (homeomorphMulEquiv (N := Fin n) fiberSphereHomeomorph 1).toMonoidHom.comp
    ((connectingHom n).comp
      (homeomorphMulEquiv (N := Fin (n + 1)) baseSphereHomeomorph north).symm.toMonoidHom)

/-- In the degree of interest this is a map from actual `π₇(S⁷)` to actual `π₆(S³)`. -/
abbrev sphereConnectingSeven :
    π_ 7 (Sphere 7) (baseSphereHomeomorph north) →*
      π_ 6 (Sphere 3) (fiberSphereHomeomorph 1) := sphereConnectingHom 6

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
