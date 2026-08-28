import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothBasic

/-!
# Actual smooth-function sheaves under open restriction

The literal nested-open equivalence is real smooth in the induced charts.
Composition identifies actual complex-valued smooth section algebras and
commutes with actual restriction. Thus restriction of the real smooth
function sheaf is the genuine smooth-function sheaf on the open manifold.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault

open HolomorphicRestriction (imageOpen flattenEquiv)

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]

/-- Literal nested-subtype flattening, at actual real smooth order. -/
def flattenSmooth (U : Opens M) (W : Opens U) :
    Diffeomorph I I W (imageOpen U W) ∞ where
  toEquiv := flattenEquiv U W
  contMDiff_toFun x := by
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact (contMDiff_subtype_val (I := I) (U := U)).contMDiffAt.comp x
      (contMDiff_subtype_val (I := I) (U := W)).contMDiffAt
  contMDiff_invFun x := by
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact (contMDiff_subtype_val (I := I) (U := imageOpen U W)).contMDiffAt

@[simp] theorem flattenSmooth_apply (U : Opens M) (W : Opens U) (x : W) :
    (flattenSmooth I U W x : M) = x.val.val := rfl

@[simp] theorem flattenSmooth_symm_apply (U : Opens M) (W : Opens U) (x : imageOpen U W) :
    ((flattenSmooth I U W).symm x).val.val = (x : M) := rfl

/-- Literal composition gives the actual complex algebra of smooth
functions on the actual open submanifold. -/
def smoothSectionEquiv (U : Opens M) (W : Opens U) :
    SmoothFunctions.Section I M (imageOpen U W) ≃ₐ[ℂ]
      SmoothFunctions.Section I U W where
  toFun f := ⟨fun x => f (flattenSmooth I U W x),
    f.contMDiff.comp (flattenSmooth I U W).contMDiff⟩
  invFun f := ⟨fun x => f ((flattenSmooth I U W).symm x),
    f.contMDiff.comp (flattenSmooth I U W).symm.contMDiff⟩
  left_inv f := ContMDiffMap.ext fun x => congrArg f ((flattenSmooth I U W).apply_symm_apply x)
  right_inv f := ContMDiffMap.ext fun x => congrArg f ((flattenSmooth I U W).symm_apply_apply x)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem smoothSectionEquiv_apply (U : Opens M) (W : Opens U)
    (f : SmoothFunctions.Section I M (imageOpen U W)) (x : W) :
    smoothSectionEquiv I U W f x = f (flattenSmooth I U W x) := rfl

/-- The genuine smooth section equivalences commute with literal restrictions. -/
def smoothPresheafIso (U : Opens M) :
    ((OpenRestriction.restriction (X := TopCat.of M) U).obj
      (SmoothFunctions.additiveSheaf I M)).obj ≅ (SmoothFunctions.additiveSheaf I U).obj :=
  NatIso.ofComponents
    (fun W => (smoothSectionEquiv I U W.unop).toAddEquiv.toAddCommGrpIso)
    (by
      intro W V h
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      apply ContMDiffMap.ext
      intro x
      rfl)

/-- Actual restriction of smooth functions is the actual smooth-function sheaf
on the open manifold, not a sheaf chosen to have the desired cohomology. -/
def smoothSheafIso (U : Opens M) :
    (OpenRestriction.restriction (X := TopCat.of M) U).obj
      (SmoothFunctions.additiveSheaf I M) ≅ SmoothFunctions.additiveSheaf I U :=
  ObjectProperty.isoMk _ (smoothPresheafIso I U)

@[simp] theorem smoothSheafIso_hom_app (U : Opens M) (W : Opens U)
    (f : SmoothFunctions.Section I M (imageOpen U W)) :
    (smoothSheafIso I U).hom.hom.app (op W) f = smoothSectionEquiv I U W f := rfl

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault
