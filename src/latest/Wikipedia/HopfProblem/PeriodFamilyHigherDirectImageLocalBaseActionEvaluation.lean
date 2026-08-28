import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageLocalBaseActionGlobal
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageLocalBaseActionGerms
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageLocalBaseActionFibre
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Actual fibre evaluation respects the local holomorphic ring

Common original neighborhood representatives identify the scalar in
fibre cohomology with evaluation of the actual holomorphic local-ring
germ. In particular multiplication by any germ in the maximal ideal
lands in the kernel of the original fibre-evaluation map. No local
freeness or residue-field base-change isomorphism is asserted.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction

open PeriodFamilyHolomorphicCohomology

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IB" => modelWithCornersSelf ℂ V

/-- Evaluation of the actual categorical holomorphic germ at the original base point. -/
abbrev baseEvaluation (P : HolomorphicPeriodMap V B) (b : B) : BaseLocalRing P b →+* ℂ :=
  HolomorphicFunctionSheaf.stalkEval IB B b

/-- The scalar evaluation retains the actual representative's base-point value. -/
theorem baseEvaluation_germ (P : HolomorphicPeriodMap V B)
    (b : B) (U : Opens B) (hb : b ∈ U) (g : Zero.BaseSection P U) :
    baseEvaluation P b ((baseFunctionPresheaf P).germ U b hb g) = g ⟨b, hb⟩ :=
  HolomorphicFunctionSheaf.stalkEval_germ IB B U b hb g

/-- Constants retain their actual complex values under local-ring evaluation. -/
theorem baseEvaluation_algebraMap (P : HolomorphicPeriodMap V B) (b : B) (c : ℂ) :
    letI := baseLocalAlgebra P b
    baseEvaluation P b (algebraMap ℂ (BaseLocalRing P b) c) = c :=
  baseEvaluation_germ P b ⊤ (by trivial)
    (OpenBaseAction.GlobalRestriction.restrictBaseFunction P ⊤
      (algebraMap ℂ (BaseFunctionAction.BaseFunction V B) c))

variable [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- The original stalk-to-fibre map is semilinear for the original local
holomorphic ring and its literal base-point evaluation. -/
theorem fibreEvaluation_local_smul (P : HolomorphicPeriodMap V B) (b : B)
    (a : BaseLocalRing P b) (x : higherDirectImageStalk P b 1) :
    letI := stalkLocalModule P b
    fibreEvaluation P b 1 (a • x) = baseEvaluation P b a • fibreEvaluation P b 1 x := by
  let := stalkLocalModule P b
  obtain ⟨U, hb, g, y, rfl, rfl⟩ := exists_common_neighborhood P b a x
  let := OpenBaseAction.neighborhoodCohomologyModule P U 1
  have hg := neighborhoodGerm_smul P b U hb g y
  have hf := neighborhoodFibreEvaluation_smul P b 1 U hb g y
  exact (congrArg (fibreEvaluation P b 1) hg.symm).trans
    ((fibreEvaluation_neighborhoodGerm_apply P b 1 U hb (g • y)).trans
      (hf.trans (congrArg₂
        (fun c : ℂ => fun z : PeriodTorusHolomorphicCohomology.H (P.point b) 1 => c • z)
        (baseEvaluation_germ P b U hb g).symm
        (fibreEvaluation_neighborhoodGerm_apply P b 1 U hb y).symm)))

/-- The actual fibre module uses the original complex action through
the actual local-ring evaluation homomorphism. -/
@[instance_reducible] def fibreLocalModule (P : HolomorphicPeriodMap V B) (b : B) :
    Module (BaseLocalRing P b) (PeriodTorusHolomorphicCohomology.H (P.point b) 1) :=
  Module.compHom (PeriodTorusHolomorphicCohomology.H (P.point b) 1) (baseEvaluation P b)

/-- The unchanged actual fibre-evaluation map is linear over the actual local ring. -/
def fibreEvaluationLocalLinearMap (P : HolomorphicPeriodMap V B) (b : B) :
    letI := stalkLocalModule P b
    letI := fibreLocalModule P b
    higherDirectImageStalk P b 1 →ₗ[BaseLocalRing P b]
      PeriodTorusHolomorphicCohomology.H (P.point b) 1 := by
  letI := stalkLocalModule P b
  letI := fibreLocalModule P b
  exact { (fibreEvaluation P b 1).hom with map_smul' := fibreEvaluation_local_smul P b }

/-- No fibre-evaluation function was changed when adding local-ring linearity. -/
@[simp] theorem fibreEvaluationLocalLinearMap_apply (P : HolomorphicPeriodMap V B)
    (b : B) (x : higherDirectImageStalk P b 1) :
    letI := stalkLocalModule P b
    letI := fibreLocalModule P b
    fibreEvaluationLocalLinearMap P b x = fibreEvaluation P b 1 x := rfl

/-- A local holomorphic germ vanishing at the point sends every actual
derived-stalk element into the original fibre-evaluation kernel. -/
theorem fibreEvaluation_local_smul_eq_zero (P : HolomorphicPeriodMap V B) (b : B)
    (a : BaseLocalRing P b) (ha : baseEvaluation P b a = 0)
    (x : higherDirectImageStalk P b 1) :
    letI := stalkLocalModule P b
    fibreEvaluation P b 1 (a • x) = 0 := by
  let := stalkLocalModule P b
  exact (fibreEvaluation_local_smul P b a x).trans
    ((congrArg (fun c : ℂ => c • fibreEvaluation P b 1 x) ha).trans (zero_smul ℂ _))

/-- Multiplication by the actual holomorphic maximal ideal is killed
after the original stalk-to-fibre evaluation, without a base-change claim. -/
theorem fibreEvaluation_maximalIdeal_smul (P : HolomorphicPeriodMap V B) (b : B)
    (a : BaseLocalRing P b) (ha : a ∈ IsLocalRing.maximalIdeal (BaseLocalRing P b))
    (x : higherDirectImageStalk P b 1) :
    letI := stalkLocalModule P b
    fibreEvaluation P b 1 (a • x) = 0 := by
  let := stalkLocalModule P b
  have hker : RingHom.ker (baseEvaluation P b) = IsLocalRing.maximalIdeal (BaseLocalRing P b) :=
    IsLocalRing.ker_eq_maximalIdeal (baseEvaluation P b)
      (HolomorphicFunctionSheaf.stalkEval_surjective IB B b)
  have ha' : a ∈ RingHom.ker (baseEvaluation P b) := by
    rwa [hker]
  exact fibreEvaluation_local_smul_eq_zero P b a ha' x

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction
