import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenBaseActionClasses
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesTwo

/-!
# Two original holomorphic coefficients give a genuine base-open linear class map

The original first-two-coefficient insertion respects multiplication
by actual holomorphic base-open functions. Thus the original two-function
period-class map is linear for the genuine coefficient-induced action
on native neighborhood cohomology. Its underlying function and actual
restricted-family class comparison are unchanged. No frame or local
generation assertion is made.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction

open PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The original first-two-coefficient insertion, now over the original
holomorphic base-open ring with pointwise multiplication. -/
def firstTwoCoefficientsBaseLinearMap (P : HolomorphicPeriodMap V B) (U : Opens B) :
    OpenClasses.PairCoefficients (V := V) U →ₗ[Zero.BaseSection P U]
      OpenClasses.Coefficients (V := V) U where
  toFun a := ![a 0, a 1, 0, 0]
  map_add' a b := by
    funext j
    fin_cases j <;> simp
  map_smul' g a := by
    funext j
    fin_cases j <;> simp

/-- The base-linear insertion is literally the previously defined insertion. -/
@[simp] theorem firstTwoCoefficientsBaseLinearMap_apply
    (P : HolomorphicPeriodMap V B) (U : Opens B) (a : OpenClasses.PairCoefficients (V := V) U) :
    firstTwoCoefficientsBaseLinearMap P U a = OpenClasses.firstTwoCoefficients U a := rfl

variable [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- The original two-function neighborhood class map is genuinely
linear over the actual holomorphic functions on the base open. -/
def pairPeriodClassBaseLinearMap (P : HolomorphicPeriodMap V B) (U : Opens B) :
    letI := neighborhoodCohomologyModule P U 1
    OpenClasses.PairCoefficients (V := V) U →ₗ[Zero.BaseSection P U]
      OpenClasses.neighborhoodCohomology P U 1 := by
  letI := neighborhoodCohomologyModule P U 1
  exact (periodClassBaseLinearMap P U).comp (firstTwoCoefficientsBaseLinearMap P U)

@[simp] theorem pairPeriodClassBaseLinearMap_apply (P : HolomorphicPeriodMap V B)
    (U : Opens B) (a : OpenClasses.PairCoefficients (V := V) U) :
    letI := neighborhoodCohomologyModule P U 1
    pairPeriodClassBaseLinearMap P U a =
      OpenClasses.periodClass P U (OpenClasses.firstTwoCoefficients U a) := rfl

/-- Strengthening the scalar ring leaves the original class function unchanged. -/
theorem pairPeriodClassBaseLinearMap_eq_original (P : HolomorphicPeriodMap V B)
    (U : Opens B) (a : OpenClasses.PairCoefficients (V := V) U) :
    letI := OpenClasses.neighborhoodCohomologyModule P U 1
    letI := neighborhoodCohomologyModule P U 1
    pairPeriodClassBaseLinearMap P U a = OpenClasses.pairPeriodClassLinearMap P U a := rfl

/-- The comparison still gives the exact original restricted-family
extension class with the same two marked coefficient functions. -/
theorem pairPeriodClassBaseLinearMap_comparison (P : HolomorphicPeriodMap V B)
    (U : Opens B) (a : OpenClasses.PairCoefficients (V := V) U) :
    letI := neighborhoodCohomologyModule P U 1
    OpenClasses.neighborhoodCohomologyEquiv P U 1 (pairPeriodClassBaseLinearMap P U a) =
      Cocycle.periodClass (Restriction.restrictedPeriods P U)
        (OpenClasses.firstTwoCoefficients U a) :=
  OpenClasses.periodClass_comparison P U _

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction
