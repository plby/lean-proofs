import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardLocalIsoBasic

/-!
# Genuine sheaf isomorphisms from compatible local section equivalences

The global section equivalences, obtained by actual sheaf gluing, are
natural for restriction. They therefore define an isomorphism of the
original sheaves. On every subopen of a member of the given cover, both
directions recover the prescribed local section equivalence.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

universe u v

namespace Wikipedia.HopfProblem.CanonicalPushforwardLocalIso

variable {X : TopCat.{u}} {κ : Type v}
  {F G : TopCat.Sheaf AddCommGrpCat.{u} X} {C : κ → Opens X}

namespace Data

variable (L : Data F G C)

/-- The original presheaves are isomorphic through the globally glued
section equivalences. -/
def presheafIso : F.obj ≅ G.obj :=
  NatIso.ofComponents (fun U => (L.sectionAddEquiv U.unop).toAddCommGrpIso)
    (by
      intro U V h
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      exact (L.sectionAddEquiv_restrict (leOfHom h.unop) s).symm)

/-- The actual sheaf isomorphism induced by the compatible local
equivalences of sections. -/
def sheafIso : F ≅ G := ObjectProperty.isoMk _ L.presheafIso

@[simp] theorem sheafIso_hom_app (U : Opens X) (s : Section F U) :
    L.sheafIso.hom.hom.app (op U) s = L.sectionAddEquiv U s := rfl

@[simp] theorem sheafIso_inv_app (U : Opens X) (s : Section G U) :
    L.sheafIso.inv.hom.app (op U) s = (L.sectionAddEquiv U).symm s := rfl

/-- Forward naturality uses the actual restriction maps of the original
sheaves. -/
theorem sheafIso_hom_app_restrict {U V : Opens X} (h : U ≤ V) (s : Section F V) :
    restrict G h (L.sheafIso.hom.hom.app (op V) s) =
      L.sheafIso.hom.hom.app (op U) (restrict F h s) :=
  L.sectionAddEquiv_restrict h s

theorem sheafIso_inv_app_restrict {U V : Opens X} (h : U ≤ V) (s : Section G V) :
    restrict F h (L.sheafIso.inv.hom.app (op V) s) =
      L.sheafIso.inv.hom.app (op U) (restrict G h s) :=
  L.sectionAddEquiv_symm_restrict h s

/-- On every chart subopen the global forward component is exactly the
prescribed local equivalence. -/
theorem sheafIso_hom_app_eq_local (i : κ) (U : Opens X) (hU : U ≤ C i)
    (s : Section F U) :
    L.sheafIso.hom.hom.app (op U) s = L.localEquiv i U hU s := by
  change L.sectionAddEquiv U s = L.localEquiv i U hU s
  rw [L.sectionAddEquiv_eq_local i U hU]

/-- On the same chart subopen the inverse is the inverse prescribed
local equivalence, not an independent choice. -/
theorem sheafIso_inv_app_eq_local (i : κ) (U : Opens X) (hU : U ≤ C i)
    (s : Section G U) :
    L.sheafIso.inv.hom.app (op U) s = (L.localEquiv i U hU).symm s := by
  change (L.sectionAddEquiv U).symm s = (L.localEquiv i U hU).symm s
  rw [L.sectionAddEquiv_eq_local i U hU]

/-- Restricting the global forward image to any chart subopen gives
the local image of the restricted original section. -/
theorem sheafIso_hom_app_restrict_chart (i : κ) {U V : Opens X}
    (h : U ≤ V) (hU : U ≤ C i) (s : Section F V) :
    restrict G h (L.sheafIso.hom.hom.app (op V) s) =
      L.localEquiv i U hU (restrict F h s) :=
  L.sectionAddEquiv_restrict_chart i h hU s

theorem sheafIso_inv_app_restrict_chart (i : κ) {U V : Opens X}
    (h : U ≤ V) (hU : U ≤ C i) (s : Section G V) :
    restrict F h (L.sheafIso.inv.hom.app (op V) s) =
      (L.localEquiv i U hU).symm (restrict G h s) :=
  L.sectionAddEquiv_symm_restrict_chart i h hU s

end Data

end Wikipedia.HopfProblem.CanonicalPushforwardLocalIso
