import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionNestedNaturality
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesTwo

/-!
# Literal restriction of the two holomorphic coefficient class maps

The source restriction is the original holomorphic restriction of each
of the two functions. Inserting the two functions as marked period
coefficients commutes with literal restriction. The genuine neighborhood
class maps therefore commute with the original cohomology-presheaf maps.
This is a naturality theorem, not a frame or generation assertion.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  {U W : Opens B}

/-- Restrict the two original holomorphic functions by their actual
holomorphic restriction algebra homomorphisms. -/
def pairRestriction (h : U ≤ W) :
    OpenClasses.PairCoefficients (V := V) W →ₗ[ℂ] OpenClasses.PairCoefficients (V := V) U where
  toFun a j := HolomorphicFunctionSheaf.restrictionAlgHom (modelWithCornersSelf ℂ V) B h (a j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coefficient restriction is literal function restriction. -/
@[simp] theorem pairRestriction_apply (h : U ≤ W)
    (a : OpenClasses.PairCoefficients (V := V) W) (j : Fin 2) (b : U) :
    pairRestriction h a j b = a j ⟨b, h b.property⟩ := rfl

/-- Inserting the two marked coefficients commutes with their actual
holomorphic restriction, including the two zero coefficients. -/
theorem restrictedCoefficients_firstTwo (h : U ≤ W)
    (a : OpenClasses.PairCoefficients (V := V) W) :
    NestedPeriodCocycle.restrictedCoefficients h (OpenClasses.firstTwoCoefficients W a) =
      OpenClasses.firstTwoCoefficients U (pairRestriction h a) := by
  funext j
  fin_cases j <;> rfl

variable [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- The original two-function class maps commute with actual restriction
of the original neighborhood cohomology-presheaf groups. -/
theorem pairPeriodClass_restrict (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (a : OpenClasses.PairCoefficients (V := V) W) :
    letI := OpenClasses.neighborhoodCohomologyModule P U 1
    letI := OpenClasses.neighborhoodCohomologyModule P W 1
    (CategoryTheory.Sheaf.cohomologyPresheaf (Zero.totalAdditiveSheaf P) 1).map
        (homOfLE (Zero.basePreimage_mono P h)).op (OpenClasses.pairPeriodClassLinearMap P W a) =
      OpenClasses.pairPeriodClassLinearMap P U (pairRestriction h a) := by
  exact (periodClass_restrict P h (OpenClasses.firstTwoCoefficients W a)).trans
    (congrArg (OpenClasses.periodClass P U) (restrictedCoefficients_firstTwo h a))

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
