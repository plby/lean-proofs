import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionBasic

/-!
# The actual restricted holomorphic sheaf is the open-submanifold sheaf

The literal nested-domain function equivalences commute with actual
restriction. They therefore form an actual isomorphism of Mathlib
additive sheaves, not an assumed local-function identification.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.HolomorphicRestriction

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]

/-- The actual section equivalences form a genuine natural presheaf isomorphism. -/
def presheafIso (U : Opens M) :
    ((OpenRestriction.restriction (X := TopCat.of M) U).obj
      (HolomorphicFunctionSheaf.additiveSheaf I M)).obj ≅
    (HolomorphicFunctionSheaf.additiveSheaf I U).obj :=
  NatIso.ofComponents
    (fun W => (sectionEquiv I U W.unop).toAddEquiv.toAddCommGrpIso)
    (by
      intro W V h
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      apply ContMDiffMap.ext
      intro x
      rfl)

/-- Genuine restriction of the actual holomorphic function sheaf is
the actual holomorphic function sheaf of the open submanifold. -/
def sheafIso (U : Opens M) :
    (OpenRestriction.restriction (X := TopCat.of M) U).obj
      (HolomorphicFunctionSheaf.additiveSheaf I M) ≅
    HolomorphicFunctionSheaf.additiveSheaf I U :=
  ObjectProperty.isoMk _ (presheafIso I U)

/-- The actual sheaf isomorphism pulls back functions by literal flattening. -/
@[simp] theorem sheafIso_hom_app (U : Opens M) (W : Opens U)
    (f : HolomorphicFunctionSheaf.Section I M (imageOpen U W)) :
    (sheafIso I U).hom.hom.app (op W) f = sectionEquiv I U W f := rfl

/-- Its inverse restores the same actual nested-domain function. -/
@[simp] theorem sheafIso_inv_app (U : Opens M) (W : Opens U)
    (f : HolomorphicFunctionSheaf.Section I U W) :
    (sheafIso I U).inv.hom.app (op W) f = (sectionEquiv I U W).symm f := rfl

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.HolomorphicRestriction
