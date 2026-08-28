import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageLocalBaseActionStalk
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkBaseActionNeighborhood

/-!
# The local-ring stalk action agrees with the original global coefficient action

The germ of an original global holomorphic function acts exactly as its
previously constructed native right-derived coefficient endomorphism.
The proof uses actual neighborhood representatives and the original
global coefficient naturality. Complex constants consequently recover
the independently defined original complex action.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction

open PeriodFamilyHolomorphicCohomology
open PeriodFamilyHolomorphicCohomology.BaseFunctionAction

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The original global function gives its actual holomorphic-function germ. -/
def globalGerm (P : HolomorphicPeriodMap V B) (b : B) :
    BaseFunction V B →+* BaseLocalRing P b :=
  ((baseFunctionPresheaf P).germ ⊤ b (by trivial)).hom.comp
    (OpenBaseAction.GlobalRestriction.restrictBaseFunction P ⊤).toRingHom

/-- Taking the actual germ after literal restriction retains the original global germ. -/
theorem globalGerm_restrict (P : HolomorphicPeriodMap V B)
    (b : B) (U : Opens B) (hb : b ∈ U) (g : BaseFunction V B) :
    (baseFunctionPresheaf P).germ U b hb
        (OpenBaseAction.GlobalRestriction.restrictBaseFunction P U g) = globalGerm P b g :=
  (baseFunctionPresheaf P).germ_res_apply (homOfLE (show U ≤ ⊤ from le_top)) b hb
    (OpenBaseAction.GlobalRestriction.restrictBaseFunction P ⊤ g)

/-- The original complex constants give the canonical complex algebra structure
on the actual holomorphic local ring. -/
@[instance_reducible] def baseLocalAlgebra (P : HolomorphicPeriodMap V B) (b : B) :
    Algebra ℂ (BaseLocalRing P b) :=
  ((globalGerm P b).comp (algebraMap ℂ (BaseFunction V B))).toAlgebra

/-- The local scalar map is the literal germ of the original constant function. -/
theorem baseLocalAlgebra_algebraMap (P : HolomorphicPeriodMap V B) (b : B) (c : ℂ) :
    letI := baseLocalAlgebra P b
    algebraMap ℂ (BaseLocalRing P b) c =
      globalGerm P b (algebraMap ℂ (BaseFunction V B) c) := rfl

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- Restricting the actual local-ring action to original global functions
recovers the independently defined native derived-stalk coefficient action. -/
theorem stalkLocalModule_global_smul (P : HolomorphicPeriodMap V B)
    (b : B) (g : BaseFunction V B) (x : higherDirectImageStalk P b 1) :
    letI := StalkBaseAction.stalkBaseModule P b 1
    letI := stalkLocalModule P b
    globalGerm P b g • x = g • x := by
  let := StalkBaseAction.stalkBaseModule P b 1
  let := stalkLocalModule P b
  obtain ⟨U, hb, y, rfl⟩ := exists_neighborhoodGerm P b x
  have hl := neighborhoodGerm_smul P b U hb
    (OpenBaseAction.GlobalRestriction.restrictBaseFunction P U g) y
  have hg := StalkBaseAction.neighborhoodGerm_restrictBaseFunction_smul P b 1 U hb g y
  exact (congrArg (fun a : BaseLocalRing P b => a • neighborhoodGerm P b 1 U hb y)
    (globalGerm_restrict P b U hb g).symm).trans (hl.symm.trans hg)

/-- Constant germs recover the independently defined native complex action. -/
theorem stalkLocalModule_algebraMap_smul (P : HolomorphicPeriodMap V B)
    (b : B) (c : ℂ) (x : higherDirectImageStalk P b 1) :
    letI := baseLocalAlgebra P b
    letI := StalkBaseAction.stalkComplexModule P b 1
    letI := stalkLocalModule P b
    algebraMap ℂ (BaseLocalRing P b) c • x = c • x := by
  let := baseLocalAlgebra P b
  let := StalkBaseAction.stalkComplexModule P b 1
  let := StalkBaseAction.stalkBaseModule P b 1
  let := stalkLocalModule P b
  exact (stalkLocalModule_global_smul P b (algebraMap ℂ (BaseFunction V B) c) x).trans
    (StalkBaseAction.stalkBaseModule_algebraMap_smul P b 1 c x)

/-- The original complex action and the genuine local-ring action form
their natural scalar tower on the unchanged derived stalk. -/
theorem stalkLocalScalarTower (P : HolomorphicPeriodMap V B) (b : B) :
    letI := baseLocalAlgebra P b
    letI := StalkBaseAction.stalkComplexModule P b 1
    letI := stalkLocalModule P b
    IsScalarTower ℂ (BaseLocalRing P b) (higherDirectImageStalk P b 1) := by
  let := baseLocalAlgebra P b
  let := StalkBaseAction.stalkComplexModule P b 1
  let := stalkLocalModule P b
  exact IsScalarTower.of_algebraMap_smul (stalkLocalModule_algebraMap_smul P b)

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction
