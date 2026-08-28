import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayCoverCocycle
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayCoverTwo
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayHigher
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverLow

/-!
# Unconditional genuine holomorphic acyclicity of the zero-ray component

The actual three-open blowup cover has genuinely acyclic members and
intersections. The actual one-cocycle splitting and actual triple-section
surjectivity proved above supply the two low-degree inputs to the original
Mayer--Vietoris sequence. Together with the proved higher-degree result,
this gives every positive Ext-defined cohomology group of the original
holomorphic function sheaf on the original toric component.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover

/-- Genuine degree-one cohomology vanishes by the actual finite cocycle calculation. -/
theorem zeroRay_h1_subsingleton : Subsingleton (CategoryTheory.Sheaf.H.{0} componentSheaf 1) := by
  have := cover_higher_subsingleton 0 0
  have := cover_higher_subsingleton 1 0
  have := cover_higher_subsingleton 2 0
  exact ThreeCover.sheaf_one_subsingleton componentSheaf cover coverOpen_eq_top cechOneExact

/-- Genuine degree-two cohomology vanishes by the actual triple-section splitting. -/
theorem zeroRay_h2_subsingleton : Subsingleton (CategoryTheory.Sheaf.H.{0} componentSheaf 2) := by
  have := cover_higher_subsingleton 0 1
  have := cover_higher_subsingleton 1 1
  have := cover_higher_subsingleton 2 1
  have := ZeroRayHigher.pair01_higher_subsingleton 0
  have := ZeroRayHigher.pair02_higher_subsingleton 0
  have := ZeroRayHigher.pair12_higher_subsingleton 0
  exact ThreeCover.sheaf_two_subsingleton componentSheaf cover coverOpen_eq_top cechTwoSurjective

/-- Every positive Mathlib Ext-defined cohomology group of the actual
holomorphic function sheaf on the actual zero-ray component is zero. -/
theorem zeroRay_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ToricCharts.CoordinateSpace 2)
        (ToricSpace.rayDivisor 0)) (n + 1)) := by
  cases n with
  | zero => exact zeroRay_h1_subsingleton
  | succ n =>
    cases n with
    | zero => exact zeroRay_h2_subsingleton
    | succ n => exact ZeroRayHigher.zeroRay_above_two_subsingleton n

theorem zeroRay_higher_eq_zero (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ToricCharts.CoordinateSpace 2)
        (ToricSpace.rayDivisor 0)) (n + 1)) : a = 0 :=
  (zeroRay_higher_subsingleton n).elim a 0

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover
