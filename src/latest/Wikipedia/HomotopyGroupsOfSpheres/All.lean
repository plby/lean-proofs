import Wikipedia.HomotopyGroupsOfSpheres.Circle
import Wikipedia.HomotopyGroupsOfSpheres.SphereTwo
import Wikipedia.HomotopyGroupsOfSpheres.SphereTwoThird
import Wikipedia.HomotopyGroupsOfSpheres.SphereThreeSix
import Wikipedia.HomotopyGroupsOfSpheres.SphereSeven

/-!
# Homotopy groups of standard spheres

All statements use the literal Euclidean unit sphere and Mathlib's native
homotopy group, at an arbitrary base point. The trivial group is `PUnit`;
the infinite cyclic group is written `Multiplicative ℤ` to match Mathlib's
multiplicative notation for homotopy groups.

* `pi1_sphere_one_mulEquiv`: `π₁(S¹) ≅ ℤ`.
* `pi2_sphere_two_mulEquiv`: `π₂(S²) ≅ ℤ`.
* `pi1_sphere_two_mulEquiv`: `π₁(S²) ≅ 0`.
* `pi2_sphere_one_mulEquiv`: `π₂(S¹) ≅ 0`.
* `pi3_sphere_two_mulEquiv`: `π₃(S²) ≅ ℤ`.
* `pi3_sphere_three_mulEquiv`: `π₃(S³) ≅ ℤ`.
* `pi6_sphere_three_mulEquiv`: `π₆(S³) ≅ ℤ/12ℤ`.
* `pi7_sphere_seven_mulEquiv`: `π₇(S⁷) ≅ ℤ`.

The accompanying `AxiomAudit` module checks their axiom dependencies.
-/
