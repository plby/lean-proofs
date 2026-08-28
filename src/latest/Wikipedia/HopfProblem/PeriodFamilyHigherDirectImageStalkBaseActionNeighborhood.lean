import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkBaseActionBasic
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkNaturalityGerms
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenBaseActionGlobalRestriction

/-!
# Original neighborhood germs preserve the native derived-stalk actions

The source is the original ambient-open Ext group. Its complex action
comes from the original cohomology-presheaf coefficient functor, and
its base-open action comes from actual holomorphic multipliers on the
original full-preimage sheaf. The target actions come independently
from the native right-derived and stalk functors.

Every genuine neighborhood germ respects complex scalars and the
restriction of each global holomorphic base function. No local-ring
action or local generation theorem is assumed.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkBaseAction

open PeriodFamilyHolomorphicCohomology
open PeriodFamilyHolomorphicCohomology.BaseFunctionAction

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The original neighborhood germ preserves the unchanged actual
complex coefficient actions in every degree. -/
theorem neighborhoodGerm_complex_smul (P : HolomorphicPeriodMap V B)
    (b : B) (q : ℕ) (U : Opens B) (hb : b ∈ U) (c : ℂ)
    (x : OpenClasses.neighborhoodCohomology P U q) :
    letI := OpenClasses.neighborhoodCohomologyModule P U q
    letI := stalkComplexModule P b q
    neighborhoodGerm P b q U hb (c • x) = c • neighborhoodGerm P b q U hb x :=
  (StalkNaturality.derivedNeighborhoodGerm_naturality_apply
    (Zero.projectionMap P) (Zero.totalScalarEnd P c) b q U hb x).symm

/-- The original neighborhood germ is genuinely complex-linear, with
independently coefficient-induced source and target modules. -/
def neighborhoodGermLinearMap (P : HolomorphicPeriodMap V B)
    (b : B) (q : ℕ) (U : Opens B) (hb : b ∈ U) :
    letI := OpenClasses.neighborhoodCohomologyModule P U q
    letI := stalkComplexModule P b q
    OpenClasses.neighborhoodCohomology P U q →ₗ[ℂ] higherDirectImageStalk P b q := by
  letI := OpenClasses.neighborhoodCohomologyModule P U q
  letI := stalkComplexModule P b q
  exact { (neighborhoodGerm P b q U hb).hom with
    map_smul' := neighborhoodGerm_complex_smul P b q U hb }

@[simp] theorem neighborhoodGermLinearMap_apply (P : HolomorphicPeriodMap V B)
    (b : B) (q : ℕ) (U : Opens B) (hb : b ∈ U)
    (x : OpenClasses.neighborhoodCohomology P U q) :
    letI := OpenClasses.neighborhoodCohomologyModule P U q
    letI := stalkComplexModule P b q
    neighborhoodGermLinearMap P b q U hb x = neighborhoodGerm P b q U hb x := rfl

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- Restricting an original global base function and then taking the
genuine neighborhood germ agrees with its native derived-stalk action. -/
theorem neighborhoodGerm_restrictBaseFunction_smul (P : HolomorphicPeriodMap V B)
    (b : B) (q : ℕ) (U : Opens B) (hb : b ∈ U) (g : BaseFunction V B)
    (x : OpenClasses.neighborhoodCohomology P U q) :
    letI := OpenBaseAction.neighborhoodCohomologyModule P U q
    letI := stalkBaseModule P b q
    neighborhoodGerm P b q U hb
        (OpenBaseAction.GlobalRestriction.restrictBaseFunction P U g • x) =
      g • neighborhoodGerm P b q U hb x := by
  let := OpenBaseAction.neighborhoodCohomologyModule P U q
  let := stalkBaseModule P b q
  exact (congrArg (neighborhoodGerm P b q U hb)
    (OpenBaseAction.GlobalRestriction.neighborhood_smul_restrictBaseFunction P U q g x)).trans
      (StalkNaturality.derivedNeighborhoodGerm_naturality_apply
        (Zero.projectionMap P) (baseMultiplyEnd P g) b q U hb x).symm

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkBaseAction
