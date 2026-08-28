import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayHigherIntersections
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverHigher

/-!
# Genuine zero-ray holomorphic cohomology vanishes above degree two

Each actual member of the three-open blowup cover and each actual
intersection has the proved higher holomorphic acyclicity. The genuine
Mayer--Vietoris theorem for three opens therefore proves this assertion
for the original Ext-defined cohomology of the original toric surface.
The lower two positive degrees require the actual section calculations.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayHigher

open ZeroRayCover

/-- Unconditional genuine higher holomorphic cohomology of E₀ above
its complex dimension, from the actual acyclic three-open cover. -/
theorem zeroRay_above_two_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} componentSheaf (n + 3)) := by
  have := cover_higher_subsingleton 0 (n + 2)
  have := cover_higher_subsingleton 1 (n + 2)
  have := cover_higher_subsingleton 2 (n + 2)
  have := pair01_higher_subsingleton (n + 1)
  have := pair02_higher_subsingleton (n + 1)
  have := pair12_higher_subsingleton (n + 1)
  have := triple_higher_subsingleton n
  exact ThreeCover.sheaf_above_two_subsingleton componentSheaf cover coverOpen_eq_top n

theorem zeroRay_above_two_eq_zero (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} componentSheaf (n + 3)) : a = 0 :=
  (zeroRay_above_two_subsingleton n).elim a 0

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayHigher
