import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInjective
import Wikipedia.HopfProblem.EllipticHigherHomologyRetractionSpecial

/-!
# Injective cohomology pullbacks for the actual special elliptic fillings

The constructed special period families instantiate the proved injectivity
of the actual integral singular-cohomology pullbacks in every degree.
The same injectivity holds for the existing map into deck invariants;
no index assertion about that invariant submodule is required.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic Elliptic.HigherHomology SingularCohomologyFree

/-- The actual special central period cover has injective integral
singular-cohomology pullback in every degree. -/
theorem specialCentralPeriodCover_cohomology_injective (j : Kind) (n : ℕ) :
    Function.Injective
      (singularCohomologyPullback (specialCentralPeriodCover j) n) :=
  periodCover_cohomology_injective j (specialLocalData j).centralPeriod n

/-- The literal map from the special period torus into the full filling
has injective integral singular-cohomology pullback in every degree. -/
theorem specialPeriodTorusIntoFilling_cohomology_injective (j : Kind) (n : ℕ) :
    Function.Injective
      (singularCohomologyPullback (specialPeriodTorusIntoFilling j) n) :=
  periodTorusIntoFilling_cohomology_injective (specialLocalData j) n

/-- The existing special-period pullback into the genuine deck-invariant
submodule is injective in every degree. -/
theorem specialCentralPeriodCoverCohomologyToInvariants_injective (j : Kind) (n : ℕ) :
    Function.Injective
      (periodCoverCohomologyToInvariants j (specialLocalData j).centralPeriod
        j.twist (mainTwist_admissible j) n) :=
  periodCoverCohomologyToInvariants_injective j (specialLocalData j).centralPeriod n

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
