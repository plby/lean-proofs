import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionNeighborhoodComparison
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionNestedPeriodCohomology
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesClasses

/-!
# Actual restriction of neighborhood period classes

For arbitrary holomorphic coefficients defined only on the larger base
open, the original native cohomology-presheaf restriction sends the
constructed period class to the class of the literal restricted
coefficients. The proof combines the genuine neighborhood comparison
square with the actual change-of-lifts comparison for period cocycles.
No extension of the coefficient functions to the whole base is assumed.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The genuine neighborhood period classes commute with the actual
cohomology-presheaf restriction for arbitrary coefficients on the
larger open, with no global extension hypothesis. -/
theorem periodClass_restrict (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (a : OpenClasses.Coefficients (V := V) W) :
    (CategoryTheory.Sheaf.cohomologyPresheaf (Zero.totalAdditiveSheaf P) 1).map
        (homOfLE (Zero.basePreimage_mono P h)).op (OpenClasses.periodClass P W a) =
      OpenClasses.periodClass P U (NestedPeriodCocycle.restrictedCoefficients h a) := by
  let := P.totalChartedSpace
  let := (Restriction.restrictedPeriods P U).totalChartedSpace
  let := (Restriction.restrictedPeriods P W).totalChartedSpace
  apply (OpenClasses.neighborhoodCohomologyEquiv P U 1).injective
  exact (neighborhoodCohomologyEquiv_restrict P h (OpenClasses.periodClass P W a)).trans
    ((congrArg (HolomorphicCohomology.pullback IT IT (NestedPeriodCocycle.familyMap P h)
      (nestedFamilyMap_isOpenEmbedding P h) (NestedPeriodCocycle.familyMap_holomorphic P h) 1)
      (OpenClasses.periodClass_comparison P W a)).trans
      ((NestedPeriodCohomology.pullback_periodClass P h a).trans
        (OpenClasses.periodClass_comparison P U
          (NestedPeriodCocycle.restrictedCoefficients h a)).symm))

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
