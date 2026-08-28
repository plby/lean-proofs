import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageGlobalRestriction
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenRestriction

/-!
# The original integer endpoint of global-to-open cohomology restriction

The endpoint is the actual open-restriction representing unit followed
by restriction of the original global integer unit. It is the actual
representing-section comparison applied to that original global unit.
No separation assumption or integer-sheaf isomorphism is used.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicSheafCohomology
open CuspNormalization.SheafCohomologyFinitePushforward
open PeriodFamilyHigherDirectImage

variable {X : TopCat.{0}} (U : Opens X)

/-- The actual integer-sheaf endpoint of the original global-to-open
restriction comparison. -/
def integerRestrictionUnit : integerSheaf (TopCat.of U) ⟶
    (OpenRestriction.restriction U).obj (integerSheaf X) :=
  OpenRestriction.representingUnit U ≫
    (OpenRestriction.restriction U).map (GlobalRestriction.globalUnit U)

/-- The endpoint is exactly the native representing-section comparison
applied to the original global integer unit. -/
theorem integerRestrictionUnit_eq_homRestrictionEquiv :
    integerRestrictionUnit U =
      OpenRestriction.homRestrictionEquiv U (integerSheaf X) (GlobalRestriction.globalUnit U) :=
  OpenRestriction.representingUnit_comp U (GlobalRestriction.globalUnit U)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
