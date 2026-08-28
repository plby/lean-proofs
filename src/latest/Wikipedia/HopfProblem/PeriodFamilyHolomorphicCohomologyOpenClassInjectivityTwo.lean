import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassInjectivityGlobal
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenBaseAction

/-!
# Injectivity of the genuine two-function neighborhood class map

The original neighborhood comparison takes a zero class to zero in the
actual restricted family's global cohomology. Its original fibre
restrictions then detect both holomorphic coefficient functions.
The independently constructed base-open module action is unchanged.
Only injectivity is asserted, not generation or existence of a frame.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassInjectivity

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- Zero-detection in the actual original `H'` follows from genuine
fibre restrictions of the actual restricted-family extension class. -/
theorem first_two_openClass_eq_zero_iff (P : HolomorphicPeriodMap V B) (U : Opens B)
    (a : OpenClasses.PairCoefficients (V := V) U) :
    OpenClasses.periodClass P U (OpenClasses.firstTwoCoefficients U a) = 0 ↔ a = 0 := by
  constructor
  · intro ha
    have hc : Cocycle.periodClass (Restriction.restrictedPeriods P U)
        (OpenClasses.firstTwoCoefficients U a) = 0 :=
      (OpenClasses.periodClass_comparison P U (OpenClasses.firstTwoCoefficients U a)).symm.trans
        ((congrArg (OpenClasses.neighborhoodCohomologyEquiv P U 1) ha).trans
          (map_zero (OpenClasses.neighborhoodCohomologyEquiv P U 1)))
    exact (first_two_periodClass_eq_zero_iff (Restriction.restrictedPeriods P U) a).mp hc
  · rintro rfl
    rw [map_zero, OpenClasses.periodClass_zero]

/-- The original base-open linear map has trivial kernel as an actual
map into the original neighborhood cohomology, with its original action. -/
theorem pairPeriodClassBaseLinearMap_eq_zero_iff (P : HolomorphicPeriodMap V B)
    (U : Opens B) (a : OpenClasses.PairCoefficients (V := V) U) :
    letI := OpenBaseAction.neighborhoodCohomologyModule P U 1
    OpenBaseAction.pairPeriodClassBaseLinearMap P U a = 0 ↔ a = 0 := by
  let := OpenBaseAction.neighborhoodCohomologyModule P U 1
  exact first_two_openClass_eq_zero_iff P U a

/-- Two arbitrary original holomorphic coefficient functions give distinct
actual neighborhood classes unless both functions already agree. -/
theorem pairPeriodClassBaseLinearMap_injective (P : HolomorphicPeriodMap V B)
    (U : Opens B) :
    letI := OpenBaseAction.neighborhoodCohomologyModule P U 1
    Function.Injective (OpenBaseAction.pairPeriodClassBaseLinearMap P U) := by
  let := OpenBaseAction.neighborhoodCohomologyModule P U 1
  intro a a' ha
  apply sub_eq_zero.mp
  apply (pairPeriodClassBaseLinearMap_eq_zero_iff P U (a - a')).mp
  rw [map_sub, ha, sub_self]

/-- The unchanged complex-linear class map is the same injective function. -/
theorem pairPeriodClassLinearMap_injective (P : HolomorphicPeriodMap V B) (U : Opens B) :
    letI := OpenClasses.neighborhoodCohomologyModule P U 1
    Function.Injective (OpenClasses.pairPeriodClassLinearMap P U) := by
  let := OpenClasses.neighborhoodCohomologyModule P U 1
  let := OpenBaseAction.neighborhoodCohomologyModule P U 1
  exact pairPeriodClassBaseLinearMap_injective P U

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassInjectivity
