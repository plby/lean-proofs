import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkBaseActionClasses
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkBaseActionFibre
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageDegreeOneEvaluation

/-!
# The original marked degree-one fibre lifts are genuinely complex-linear

The already constructed constant-character lifts preserve the complex
action induced independently by the actual coefficient sheaf maps.
They give a complex-linear right inverse of the original degree-one
fibre evaluation. For an open complex base that evaluation still has
the already proved nonzero kernel; no raw-stalk isomorphism is asserted.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkBaseAction

open PeriodFamilyHolomorphicCohomology

section GeneralBase

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The original negative marked inverse gives a complex-linear lift
of the two genuine fibre coordinates. -/
def oneFibreLiftLinearMap (P : HolomorphicPeriodMap V B) (b : B) :
    letI := stalkComplexModule P b 1
    (Fin 2 → ℂ) →ₗ[ℂ] higherDirectImageStalk P b 1 := by
  letI := stalkComplexModule P b 1
  exact (firstPeriodStalkClassLinearMap P b).comp
    (-(MarkedLinear.firstDbarEquiv (P.point b)).symm.toLinearMap)

@[simp] theorem oneFibreLiftLinearMap_apply (P : HolomorphicPeriodMap V B)
    (b : B) (c : Fin 2 → ℂ) :
    letI := stalkComplexModule P b 1
    oneFibreLiftLinearMap P b c = oneFibreLift P b c := rfl

/-- The original actual cohomology class lift is complex-linear for
the original coefficient-induced source and target actions. -/
def cohomologyFibreLiftLinearMap (P : HolomorphicPeriodMap V B) (b : B) :
    letI := stalkComplexModule P b 1
    PeriodTorusHolomorphicCohomology.H (P.point b) 1 →ₗ[ℂ]
      higherDirectImageStalk P b 1 := by
  letI := stalkComplexModule P b 1
  exact (oneFibreLiftLinearMap P b).comp
    (PeriodTorusHolomorphicCohomology.h1Equiv (P.point b)).toLinearMap

@[simp] theorem cohomologyFibreLiftLinearMap_apply (P : HolomorphicPeriodMap V B)
    (b : B) (a : PeriodTorusHolomorphicCohomology.H (P.point b) 1) :
    letI := stalkComplexModule P b 1
    cohomologyFibreLiftLinearMap P b a = cohomologyFibreLift P b a := rfl

variable [T2Space B]

/-- The same original lift is a genuine complex-linear right inverse
of the native degree-one fibre evaluation. -/
theorem fibreEvaluationLinearMap_comp_lift (P : HolomorphicPeriodMap V B) (b : B) :
    letI := stalkComplexModule P b 1
    (fibreEvaluationLinearMap P b 1).comp (cohomologyFibreLiftLinearMap P b) =
      LinearMap.id := by
  let := stalkComplexModule P b 1
  apply LinearMap.ext
  intro a
  exact fibreEvaluation_cohomologyFibreLift P b a

/-- Complex-linear packaging leaves the proved actual surjectivity unchanged. -/
theorem fibreEvaluationLinearMap_one_surjective (P : HolomorphicPeriodMap V B) (b : B) :
    letI := stalkComplexModule P b 1
    Function.Surjective (fibreEvaluationLinearMap P b 1) :=
  fibreEvaluation_one_surjective P b

end GeneralBase

/-- On every original open complex base the same genuine complex-linear
evaluation has the explicit nonzero kernel already proved for its native map. -/
theorem fibreEvaluationLinearMap_one_not_injective (U : Opens ℂ)
    (P : HolomorphicPeriodMap ℂ U) (b : U) :
    letI := stalkComplexModule P b 1
    ¬ Function.Injective (fibreEvaluationLinearMap P b 1) :=
  FibreKernel.fibreEvaluation_one_not_injective U P b

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkBaseAction
