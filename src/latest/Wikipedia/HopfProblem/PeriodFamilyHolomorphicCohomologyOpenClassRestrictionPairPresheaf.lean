import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionPairNaturality

/-!
# The natural two-function map to original neighborhood cohomology

The source additive presheaf consists of two actual holomorphic functions
on each original base open, with literal function restriction. The genuine
two-function period-class maps give a natural transformation into the
original cohomology presheaf evaluated on the actual full base preimages.
Its components are the original complex-linear maps, forgotten to additive
maps using their original sheaf-induced scalar structures.

This construction proves neither a frame nor generation or invertibility.
-/

noncomputable section

open TopologicalSpace CategoryTheory Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The additive presheaf of two original holomorphic base-open functions,
with their literal componentwise holomorphic restriction maps. -/
def pairCoefficientPresheaf : (Opens B)ᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj U := AddCommGrpCat.of (OpenClasses.PairCoefficients (V := V) U.unop)
  map h := AddCommGrpCat.ofHom (pairRestriction (V := V) (leOfHom h.unop)).toAddMonoidHom
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    funext j
    apply ContMDiffMap.ext
    intro b
    rfl
  map_comp h k := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    funext j
    apply ContMDiffMap.ext
    intro b
    rfl

/-- The actual presheaf restriction is the original two-function
complex-linear restriction, with only its additive structure retained. -/
@[simp] theorem pairCoefficientPresheaf_map_apply {U W : Opens B} (h : U ≤ W)
    (a : OpenClasses.PairCoefficients (V := V) W) :
    (pairCoefficientPresheaf (V := V) (B := B)).map (homOfLE h).op a =
      pairRestriction h a := rfl

/-- Each restricted component retains the value of the original function
at the same original base point. -/
@[simp] theorem pairCoefficientPresheaf_map_apply_apply {U W : Opens B} (h : U ≤ W)
    (a : OpenClasses.PairCoefficients (V := V) W) (j : Fin 2) (b : U) :
    ((pairCoefficientPresheaf (V := V) (B := B)).map (homOfLE h).op a :
      OpenClasses.PairCoefficients (V := V) U) j b = a j ⟨b, h b.property⟩ := rfl

variable [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- The genuine two-function period classes form a natural transformation
to the original degree-one cohomology presheaf on full base preimages. -/
def pairPeriodClassNatTrans (P : HolomorphicPeriodMap V B) :
    pairCoefficientPresheaf (V := V) (B := B) ⟶
      (Opens.map (Zero.projectionMap P)).op ⋙
        CategoryTheory.Sheaf.cohomologyPresheaf (Zero.totalAdditiveSheaf P) 1 where
  app U := by
    letI := OpenClasses.neighborhoodCohomologyModule P U.unop 1
    exact AddCommGrpCat.ofHom (Y := OpenClasses.neighborhoodCohomology P U.unop 1)
      (OpenClasses.pairPeriodClassLinearMap P U.unop).toAddMonoidHom
  naturality U W h := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    exact (pairPeriodClass_restrict P (leOfHom h.unop) a).symm

/-- Every component is the original native complex-linear period-class
map itself, evaluated on the original two holomorphic functions. -/
@[simp] theorem pairPeriodClassNatTrans_app (P : HolomorphicPeriodMap V B)
    (U : Opens B) (a : OpenClasses.PairCoefficients (V := V) U) :
    letI := OpenClasses.neighborhoodCohomologyModule P U 1
    (pairPeriodClassNatTrans P).app (op U) a =
      OpenClasses.pairPeriodClassLinearMap P U a := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
