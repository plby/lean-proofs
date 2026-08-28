import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardPositiveCartier
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardPositiveSheaf

/-!
# The positive infinity line and its reduced geometric divisor

This is the actual dual of the fixed sphere ideal bundle.  Its global
native holomorphic section has finite coefficient `1` and reciprocal
coefficient `w`, and is an actual global section of the native section
sheaf.  The genuine Cartier section has sole zero infinity, order one
there and order zero at every finite point.  Thus its geometric divisor
is the reduced point at infinity; no degree or torsion assumption is used.
-/

open Bundle Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Positive

/-- Exact support of the zero divisor of the original native holomorphic section. -/
theorem zeroSet_eq_singleton :
    {p : RiemannSphere | sectionValue p = 0} = {(∞ : RiemannSphere)} :=
  Set.ext section_eq_zero_iff

/-- Its multiplicity is computed from the actual native reciprocal-chart coefficient. -/
theorem simple_zero :
    analyticOrderAt (fun w : ℂ => data.localCoefficient sectionValue true
      (RiemannSphere.infinityParametrization w)) 0 = 1 :=
  section_infinity_simple_zero

/-- Every finite point has order zero in the actual native finite chart. -/
theorem section_finite_analyticOrderAt (z : ℂ) :
    analyticOrderAt (fun u : ℂ =>
      data.localCoefficient sectionValue false (u : RiemannSphere)) z = 0 := by
  have h : (fun u : ℂ => data.localCoefficient sectionValue false (u : RiemannSphere)) =
      (fun _ : ℂ => (1 : ℂ)) := funext section_finite_coefficient
  rw [h]
  exact analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Positive
