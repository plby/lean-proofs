import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionFamilyDifference
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleClass
import Wikipedia.HopfProblem.HolomorphicPicardCechRefinementClass
import Wikipedia.HopfProblem.HolomorphicPicardCechCoboundaryClass

/-!
# The original pulled-back period class equals the native restricted-family class

Two actual refinement maps and the genuine local holomorphic coboundary
give actual maps of the constructed Čech extensions. Their native Ext
classes agree. Thus the independently chosen local inverses in the
restricted family do not add an assumed comparison to the result.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicPicard.CechExtension

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- Genuine Ext classes of the literal pulled-back period cocycle and
the independently constructed native restricted-family cocycle coincide. -/
theorem familyPullbackCocycle_classOf (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) :
    classOf (familyPullbackCocycle P A a) (familyPullbackCover_covers P A) =
      Cocycle.periodClass (Restriction.restrictedPeriods P A) (restrictCoefficients A a) := by
  have h := classOf_eq_of_coboundary
    (familyCommonPullbackCocycle P A a) (familyCommonNativeCocycle P A a)
    (familyCommonCover_covers P A) (familyComparisonCochain P A a)
    (familyCommonCocycle_sub_eq_coboundary P A a)
  exact (classOf_refinement Prod.fst (fun _ => inf_le_left)
    (familyPullbackCocycle P A a) (familyPullbackCover_covers P A)
    (familyCommonCover_covers P A)).symm.trans
      (h.trans (classOf_refinement Prod.snd (fun _ => inf_le_right)
        (Cocycle.cocycle (Restriction.restrictedPeriods P A) (restrictCoefficients A a))
        (Cocycle.coverOpen_covers (Restriction.restrictedPeriods P A))
        (familyCommonCover_covers P A)))

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
