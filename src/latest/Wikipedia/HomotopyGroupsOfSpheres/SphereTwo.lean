import Wikipedia.HomotopyGroupsOfSpheres.Basic
import Wikipedia.HopfProblem.SphereHomologySimplyConnectedPiTwo

/-! # The first and second homotopy groups of the two-sphere -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

/-- The first homotopy group of the standard two-sphere is trivial. -/
theorem pi1_sphere_two_subsingleton (x : Sphere 2) :
    Subsingleton (π_ 1 (Sphere 2) x) :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.injective.subsingleton

/-- `π₁(S²) ≅ 0`, expressed as an isomorphism to the one-element group. -/
def pi1_sphere_two_mulEquiv (x : Sphere 2) : π_ 1 (Sphere 2) x ≃* PUnit := by
  letI := pi1_sphere_two_subsingleton x
  letI := uniqueOfSubsingleton (1 : π_ 1 (Sphere 2) x)
  exact MulEquiv.ofUnique

/-- The second homotopy group of the standard two-sphere is infinite cyclic. -/
def pi2_sphere_two_mulEquiv (x : Sphere 2) :
    π_ 2 (Sphere 2) x ≃* Multiplicative ℤ :=
  HopfProblem.SphereHomology.sphereTwoPiTwoMulEquiv x

end Wikipedia.HomotopyGroupsOfSpheres
