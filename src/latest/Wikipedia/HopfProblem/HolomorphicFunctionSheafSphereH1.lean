import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Solvable
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Lifting
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Ext

/-!
# Genuine first holomorphic sheaf cohomology of the sphere

The sheaf is the actual additive sheaf of bundled holomorphic functions
on opens of the constructed analytic Riemann sphere. The cohomology is
mathlib's `Sheaf.H`, defined by `Ext` from the constant integer sheaf.

The arbitrary-cover Cousin solver constructs actual coboundary sections.
Local lifting and sheaf gluing turn this into lifting in every short
exact sequence beginning in the holomorphic-function sheaf. An actual
injective presentation and the Ext exact sequence prove `H¹(P¹, O) = 0`.

No Cartan theorem, Stein property, Čech comparison, or cohomological
vanishing is an input. Nothing in this file asserts higher cohomology
vanishing for the global threefold.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

/-- The proved degree-one comparison needed here: solvability of actual
one-cocycles on every open cover implies vanishing of genuine sheaf H¹. -/
theorem subsingleton_h1_of_cechOneVanishing {X : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (hF : CechOneVanishing F) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F 1) :=
  subsingleton_h1_of_globalLifting F (globalLifting_of_cechOneVanishing hF)

/-- Actual global lifting for short exact sequences with the sphere's
holomorphic-function sheaf as their first term. -/
theorem sphere_globalLifting : GlobalLifting sphereSheaf :=
  globalLifting_of_cechOneVanishing sphere_cechOneVanishing

/-- The group operations are exactly the existing operations on Ext,
made explicit for the actual sphere-sheaf abbreviation. -/
instance sphereH1AddCommGroup : AddCommGroup (CategoryTheory.Sheaf.H.{0} sphereSheaf 1) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- Genuine `H¹(P¹, O)` is the zero additive group. -/
theorem sphere_h1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} sphereSheaf 1) :=
  subsingleton_h1_of_cechOneVanishing sphereSheaf sphere_cechOneVanishing

/-- Every genuine degree-one holomorphic sheaf-cohomology class on the
constructed Riemann sphere is zero, with no additional hypotheses. -/
theorem sphere_h1_eq_zero (x : CategoryTheory.Sheaf.H.{0} sphereSheaf 1) : x = 0 :=
  h1_eq_zero_of_globalLifting sphereSheaf sphere_globalLifting x

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
