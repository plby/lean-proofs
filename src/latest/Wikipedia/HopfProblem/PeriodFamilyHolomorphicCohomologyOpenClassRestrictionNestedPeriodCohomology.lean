import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicCohomologyCech
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionFamilyEmbeddings
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionNestedPeriodCocycle

/-!
# Native holomorphic cohomology pullback of nested-family period classes

The actual cohomology pullback and the original period-cocycle pullback
use the same all-open morphism of holomorphic coefficient sheaves. The
proved Čech-class transport and genuine change-of-primitive comparison
therefore identify the native cohomology classes for arbitrary
coefficients defined only on the larger base open.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.NestedPeriodCohomology

open HolomorphicPicard.CechExtension

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]
  {U W : Opens B}

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- On every actual ambient open, both coefficient maps are literal
composition with the original nested-family inclusion. -/
theorem pushforwardCoefficientMap_eq (P : HolomorphicPeriodMap V B) (h : U ≤ W) :
    letI := (Restriction.restrictedPeriods P U).totalChartedSpace
    letI := (Restriction.restrictedPeriods P W).totalChartedSpace
    HolomorphicCohomology.pushforwardCoefficientMap IT IT
        (NestedPeriodCocycle.familyMap P h) (nestedFamilyMap_isOpenEmbedding P h)
        (NestedPeriodCocycle.familyMap_holomorphic P h) =
      NestedPeriodCocycle.coefficientPullback P h := by
  let := (Restriction.restrictedPeriods P U).totalChartedSpace
  let := (Restriction.restrictedPeriods P W).totalChartedSpace
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext A
  apply ConcreteCategory.hom_ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

/-- Actual holomorphic cohomology pullback preserves the original period
class with literal restriction of coefficients defined only on the larger open. -/
theorem pullback_periodClass (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (a : Cocycle.Coefficients V W) :
    letI := (Restriction.restrictedPeriods P U).totalChartedSpace
    letI := (Restriction.restrictedPeriods P W).totalChartedSpace
    HolomorphicCohomology.pullback IT IT
        (NestedPeriodCocycle.familyMap P h) (nestedFamilyMap_isOpenEmbedding P h)
        (NestedPeriodCocycle.familyMap_holomorphic P h) 1
        (Cocycle.periodClass (Restriction.restrictedPeriods P W) a) =
      Cocycle.periodClass (Restriction.restrictedPeriods P U)
        (NestedPeriodCocycle.restrictedCoefficients h a) := by
  let := (Restriction.restrictedPeriods P U).totalChartedSpace
  let := (Restriction.restrictedPeriods P W).totalChartedSpace
  have hc := HolomorphicCohomology.pullback_classOf IT IT
    (NestedPeriodCocycle.familyMap P h) (nestedFamilyMap_isOpenEmbedding P h)
    (NestedPeriodCocycle.familyMap_holomorphic P h)
    (Cocycle.cocycle (Restriction.restrictedPeriods P W) a)
    (Cocycle.coverOpen_covers (Restriction.restrictedPeriods P W))
  have he := congrArg (fun κ => CechFibre.pullbackCocycle
    (NestedPeriodCocycle.familyMap P h) κ
    (Cocycle.cocycle (Restriction.restrictedPeriods P W) a))
    (pushforwardCoefficientMap_eq P h)
  exact hc.trans ((congrArg (fun d => classOf d
    (NestedPeriodCocycle.pullbackCover_covers P h)) he).trans
      (NestedPeriodCocycle.pullbackCocycle_classOf P h a))

end OpenClassRestriction.NestedPeriodCohomology
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
