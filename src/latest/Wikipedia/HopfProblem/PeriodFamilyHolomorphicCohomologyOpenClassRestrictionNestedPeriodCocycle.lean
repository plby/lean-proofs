import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionNestedPeriodCocycleDifference
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleClass
import Wikipedia.HopfProblem.HolomorphicPicardCechRefinementClass
import Wikipedia.HopfProblem.HolomorphicPicardCechCoboundaryClass

/-!
# Actual period classes restrict between nested base opens

For coefficients defined only on the larger open, the genuine Čech
pullback along the original nested-family map has the same native Ext
class as the independently constructed smaller-family period cocycle.
The proof uses two actual refinement maps and the holomorphic change of
primitive, without identifying the independently chosen lift covers.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.NestedPeriodCocycle

open HolomorphicPicard.CechExtension

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]
  {U W : Opens B}

/-- The actual pulled-back period cocycle and the native restricted-coefficient
cocycle have equal classes in the genuine sheaf Ext group. -/
theorem pullbackCocycle_classOf (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (a : Cocycle.Coefficients V W) :
    classOf (pullbackCocycle P h a) (pullbackCover_covers P h) =
      Cocycle.periodClass (Restriction.restrictedPeriods P U) (restrictedCoefficients h a) := by
  have hc := classOf_eq_of_coboundary
    (commonPullbackCocycle P h a) (commonNativeCocycle P h a)
    (commonCover_covers P h) (comparisonCochain P h a)
    (commonCocycle_sub_eq_coboundary P h a)
  exact (classOf_refinement Prod.fst (fun _ => inf_le_left)
    (pullbackCocycle P h a) (pullbackCover_covers P h)
    (commonCover_covers P h)).symm.trans
      (hc.trans (classOf_refinement Prod.snd (fun _ => inf_le_right)
        (Cocycle.cocycle (Restriction.restrictedPeriods P U) (restrictedCoefficients h a))
        (Cocycle.coverOpen_covers (Restriction.restrictedPeriods P U))
        (commonCover_covers P h)))

end OpenClassRestriction.NestedPeriodCocycle
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
