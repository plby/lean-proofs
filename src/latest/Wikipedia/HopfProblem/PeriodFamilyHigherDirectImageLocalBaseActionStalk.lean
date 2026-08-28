import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageLocalBaseActionPresheaf
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreComparison

/-!
# The original local holomorphic ring acts on the native degree-one derived stalk

The genuine module-presheaf stalk action is expressed on the original
right-derived pushforward stalk through its already proved canonical
stalk comparison. Original neighborhood germs retain the literal local
coefficient multiplication. No fibre coordinates, basis, local freeness,
or base-change assertion is used.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction

open PeriodFamilyHolomorphicCohomology

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The previously proved canonical comparison of the two original stalk groups. -/
def stalkComparison (P : HolomorphicPeriodMap V B) (b : B) :
    higherDirectImageStalk P b 1 ≃+ (neighborhoodPresheaf P).stalk b :=
  (SheafHigherDirectImage.stalkCohomologyPresheafIso
    (Zero.projectionMap P) (Zero.totalAdditiveSheaf P) 1 b).addCommGroupIsoToAddEquiv

/-- The original derived neighborhood germ is exactly the original
cohomology-presheaf germ under the canonical comparison. -/
theorem stalkComparison_neighborhoodGerm (P : HolomorphicPeriodMap V B)
    (b : B) (U : Opens B) (hb : b ∈ U)
    (x : OpenClasses.neighborhoodCohomology P U 1) :
    stalkComparison P b (neighborhoodGerm P b 1 U hb x) =
      (neighborhoodPresheaf P).germ U b hb x :=
  (stalkComparison P b).apply_symm_apply _

/-- Every original derived-stalk element has an actual original neighborhood representative. -/
theorem exists_neighborhoodGerm (P : HolomorphicPeriodMap V B) (b : B)
    (x : higherDirectImageStalk P b 1) :
    ∃ (U : Opens B) (hb : b ∈ U) (y : OpenClasses.neighborhoodCohomology P U 1),
      neighborhoodGerm P b 1 U hb y = x := by
  obtain ⟨U, hb, y, hy⟩ := (neighborhoodPresheaf P).exists_germ_eq (stalkComparison P b x)
  exact ⟨U, hb, y, (stalkComparison P b).injective
    ((stalkComparison_neighborhoodGerm P b U hb y).trans hy)⟩

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual local holomorphic ring acts on the original derived stalk
through the genuine module-presheaf stalk and canonical native comparison. -/
@[instance_reducible] def stalkLocalModule (P : HolomorphicPeriodMap V B) (b : B) :
    Module (BaseLocalRing P b) (higherDirectImageStalk P b 1) := by
  letI := neighborhoodStalkModule P b
  exact (stalkComparison P b).module (BaseLocalRing P b)

/-- The local-ring action is precisely the canonical comparison of the
genuine coefficient-induced presheaf-stalk action. -/
theorem stalkLocalModule_smul (P : HolomorphicPeriodMap V B) (b : B)
    (a : BaseLocalRing P b) (x : higherDirectImageStalk P b 1) :
    letI := neighborhoodStalkModule P b
    letI := stalkLocalModule P b
    a • x = (stalkComparison P b).symm (a • stalkComparison P b x) := rfl

/-- The canonical native comparison respects the actual local-ring action. -/
theorem stalkComparison_smul (P : HolomorphicPeriodMap V B) (b : B)
    (a : BaseLocalRing P b) (x : higherDirectImageStalk P b 1) :
    letI := neighborhoodStalkModule P b
    letI := stalkLocalModule P b
    stalkComparison P b (a • x) = a • stalkComparison P b x := by
  let := neighborhoodStalkModule P b
  let := stalkLocalModule P b
  exact (congrArg (stalkComparison P b) (stalkLocalModule_smul P b a x)).trans
    ((stalkComparison P b).apply_symm_apply _)

/-- The actual derived neighborhood germ respects a holomorphic function
defined only on that neighborhood and its original local-ring germ. -/
theorem neighborhoodGerm_smul (P : HolomorphicPeriodMap V B)
    (b : B) (U : Opens B) (hb : b ∈ U) (g : Zero.BaseSection P U)
    (x : OpenClasses.neighborhoodCohomology P U 1) :
    letI := OpenBaseAction.neighborhoodCohomologyModule P U 1
    letI := stalkLocalModule P b
    neighborhoodGerm P b 1 U hb (g • x) =
      (baseFunctionPresheaf P).germ U b hb g • neighborhoodGerm P b 1 U hb x := by
  let := OpenBaseAction.neighborhoodCohomologyModule P U 1
  let := neighborhoodStalkModule P b
  let := stalkLocalModule P b
  apply (stalkComparison P b).injective
  exact (stalkComparison_neighborhoodGerm P b U hb (g • x)).trans
    ((neighborhoodPresheaf_germ_smul P b U hb g x).trans
      ((congrArg (fun y : (neighborhoodPresheaf P).stalk b =>
        (baseFunctionPresheaf P).germ U b hb g • y)
        (stalkComparison_neighborhoodGerm P b U hb x).symm).trans
        (stalkComparison_smul P b ((baseFunctionPresheaf P).germ U b hb g)
          (neighborhoodGerm P b 1 U hb x)).symm))

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction
