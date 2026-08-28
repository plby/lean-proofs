import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesLinear

/-!
# Two holomorphic coefficients give genuine native neighborhood classes

Insert two original holomorphic base-open functions as the first two
marked period coefficients, with the last two zero. The constructed
period-class map then gives a genuine complex-linear map into the
original neighborhood cohomology group. No claim of a basis, a sheaf
frame, or compatibility between different base opens is made here.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClasses

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- Two actual holomorphic functions on the original base open. -/
abbrev PairCoefficients (U : Opens B) :=
  Fin 2 → HolomorphicFunctionSheaf.Section (modelWithCornersSelf ℂ V) B U

/-- Insert the first two original marked coefficients and set the
last two to the actual zero holomorphic functions. -/
def firstTwoCoefficients (U : Opens B) :
    PairCoefficients (V := V) U →ₗ[ℂ] Coefficients (V := V) U where
  toFun a := ![a 0, a 1, 0, 0]
  map_add' a b := by
    funext j
    fin_cases j <;> simp
  map_smul' c a := by
    funext j
    fin_cases j <;> simp

@[simp] theorem firstTwoCoefficients_apply (U : Opens B) (a : PairCoefficients (V := V) U) :
    firstTwoCoefficients U a = ![a 0, a 1, 0, 0] := rfl

/-- Evaluation retains the literal two marked coefficients and two zeros. -/
theorem firstTwoCoefficients_values (U : Opens B) (a : PairCoefficients (V := V) U) (b : U) :
    (fun j => firstTwoCoefficients U a j b) = ![a 0 b, a 1 b, 0, 0] := by
  funext j
  fin_cases j <;> rfl

variable [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- The genuine two-function class map into the original native
cohomology-presheaf group of the actual full base preimage. -/
def pairPeriodClassLinearMap (P : HolomorphicPeriodMap V B) (U : Opens B) :
    letI := neighborhoodCohomologyModule P U 1
    PairCoefficients (V := V) U →ₗ[ℂ] neighborhoodCohomology P U 1 := by
  letI := neighborhoodCohomologyModule P U 1
  exact (periodClassLinearMap P U).comp (firstTwoCoefficients U)

@[simp] theorem pairPeriodClassLinearMap_apply (P : HolomorphicPeriodMap V B)
    (U : Opens B) (a : PairCoefficients (V := V) U) :
    letI := neighborhoodCohomologyModule P U 1
    pairPeriodClassLinearMap P U a = periodClass P U (firstTwoCoefficients U a) := rfl

/-- The comparison remains the actual original restricted-family
period extension class with those two literal coefficients. -/
theorem pairPeriodClass_comparison (P : HolomorphicPeriodMap V B) (U : Opens B)
    (a : PairCoefficients (V := V) U) :
    letI := neighborhoodCohomologyModule P U 1
    neighborhoodCohomologyEquiv P U 1 (pairPeriodClassLinearMap P U a) =
      Cocycle.periodClass (Restriction.restrictedPeriods P U) (firstTwoCoefficients U a) :=
  periodClass_comparison P U _

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClasses
