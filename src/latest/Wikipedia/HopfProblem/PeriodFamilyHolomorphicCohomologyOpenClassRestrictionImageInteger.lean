import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionImageIntegerComposition
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionUnit

/-!
# The open-image integer endpoint is the original restriction unit

The native sheafification endpoint for the actual open-image functor agrees
with the already constructed global-to-open restriction endpoint. Equality
is proved by their actual constant-presheaf degree-unit formulas.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.ImageInteger

open HolomorphicSheafCohomology

/-- On the original open-image functor, the native sheafification endpoint is
exactly the frozen integer endpoint of actual global-to-open restriction. -/
theorem unit_openImage {X : TopCat.{0}} (A : Opens X) :
    unit (T := TopCat.of A) (X := X) (OpenRestriction.openImage A) =
      integerRestrictionUnit A :=
  (unit_unique (T := TopCat.of A) (X := X)
    (OpenRestriction.openImage A) (integerRestrictionUnit A)
    (degreeUnit_integerRestrictionUnit A)).symm

end OpenClassRestriction.ImageInteger
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
