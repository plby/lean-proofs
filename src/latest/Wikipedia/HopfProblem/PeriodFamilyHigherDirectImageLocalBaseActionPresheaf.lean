import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageLocalBaseActionRestriction
import Wikipedia.HopfProblem.HolomorphicFunctionSheafLocalRing
import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# The original neighborhood cohomology presheaf as a module presheaf

The coefficient-induced actions and proved arbitrary nested-open
semilinearity make the original degree-one cohomology presheaf a
presheaf of modules over the original holomorphic function presheaf.
Its underlying additive presheaf is unchanged, definitionally.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction

open PeriodFamilyHolomorphicCohomology

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The original presheaf of holomorphic functions on the original base. -/
abbrev baseFunctionPresheaf (_P : HolomorphicPeriodMap V B) :
    TopCat.Presheaf CommRingCat.{0} (TopCat.of B) :=
  HolomorphicFunctionSheaf.presheaf (modelWithCornersSelf ℂ V) B

/-- The actual categorical holomorphic-function stalk, with its original ring operations. -/
abbrev BaseLocalRing (P : HolomorphicPeriodMap V B) (b : B) : CommRingCat.{0} :=
  (baseFunctionPresheaf P).stalk b

/-- The unchanged additive degree-one cohomology presheaf on original full preimages. -/
abbrev neighborhoodPresheaf (P : HolomorphicPeriodMap V B) :
    TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of B) :=
  (Opens.map (Zero.projectionMap P)).op ⋙
    CategoryTheory.Sheaf.cohomologyPresheaf (Zero.totalAdditiveSheaf P) 1

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The genuine local coefficient actions form a presheaf of modules
on precisely the original additive neighborhood-cohomology presheaf. -/
def neighborhoodModulePresheaf (P : HolomorphicPeriodMap V B) :
    PresheafOfModules.{0} (baseFunctionPresheaf P ⋙ forget₂ CommRingCat RingCat) := by
  letI (U : (Opens (TopCat.of B))ᵒᵖ) :
      Module ((baseFunctionPresheaf P ⋙ forget₂ CommRingCat RingCat).obj U)
        ((neighborhoodPresheaf P).obj U) :=
    OpenBaseAction.neighborhoodCohomologyModule P U.unop 1
  exact PresheafOfModules.ofPresheaf (neighborhoodPresheaf P) (by
    intro U W h g x
    exact neighborhoodRestriction_smul P (leOfHom h.unop) g x)

/-- No underlying cohomology object or restriction map was replaced. -/
@[simp] theorem neighborhoodModulePresheaf_presheaf (P : HolomorphicPeriodMap V B) :
    (neighborhoodModulePresheaf P).presheaf = neighborhoodPresheaf P := rfl

/-- Mathlib's genuine module-presheaf stalk construction gives the
action of the original local ring on the original cohomology-presheaf stalk. -/
@[instance_reducible] def neighborhoodStalkModule (P : HolomorphicPeriodMap V B) (b : B) :
    Module (BaseLocalRing P b) ((neighborhoodPresheaf P).stalk b) :=
  (neighborhoodModulePresheaf P).instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier b

/-- On original common-open representatives, the genuine local-ring
action is the original holomorphic base-function coefficient action. -/
theorem neighborhoodPresheaf_germ_smul (P : HolomorphicPeriodMap V B)
    (b : B) (U : Opens B) (hb : b ∈ U) (g : Zero.BaseSection P U)
    (x : OpenClasses.neighborhoodCohomology P U 1) :
    letI := OpenBaseAction.neighborhoodCohomologyModule P U 1
    letI := neighborhoodStalkModule P b
    (neighborhoodPresheaf P).germ U b hb (g • x) =
      (baseFunctionPresheaf P).germ U b hb g • (neighborhoodPresheaf P).germ U b hb x := by
  let := OpenBaseAction.neighborhoodCohomologyModule P U 1
  let := neighborhoodStalkModule P b
  exact PresheafOfModules.germ_smul (neighborhoodModulePresheaf P) b U hb g x

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction
