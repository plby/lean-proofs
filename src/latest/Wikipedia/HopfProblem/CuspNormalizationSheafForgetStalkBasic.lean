import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Forgetting a commutative ring structure commutes with actual stalks

The forgetful functor from commutative rings to additive commutative
groups preserves filtered colimits. Applying that proved preservation
to the actual neighbourhood diagram gives a canonical additive
equivalence between the two actual categorical stalks.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafForgetStalk

variable {X : TopCat.{0}}

/-- The existing composite forgetful functor retains the actual
underlying additive group of a commutative ring. -/
abbrev forgetToAdd : CommRingCat.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

/-- Preservation is inherited from the two actual forgetful functors. -/
instance forgetToAdd_preservesFilteredColimits : PreservesFilteredColimits forgetToAdd :=
  comp_preservesFilteredColimits (forget₂ CommRingCat RingCat)
    (forget₂ RingCat AddCommGrpCat)

/-- The actual additive presheaf underlying a commutative-ring presheaf. -/
abbrev additivePresheaf (F : TopCat.Presheaf CommRingCat.{0} X) :
    TopCat.Presheaf AddCommGrpCat.{0} X :=
  F ⋙ forgetToAdd

/-- The comparison is the inverse of the actual colimit-preservation
isomorphism on the neighbourhood diagram, not an assumed stalk formula. -/
def stalkIso (F : TopCat.Presheaf CommRingCat.{0} X) (x : X) :
    (additivePresheaf F).stalk x ≅ forgetToAdd.obj (F.stalk x) :=
  (preservesColimitIso forgetToAdd ((OpenNhds.inclusion x).op ⋙ F)).symm

/-- The canonical comparison commutes with the actual colimit inclusions
that define section germs. -/
@[reassoc] theorem germ_stalkIso_hom (F : TopCat.Presheaf CommRingCat.{0} X)
    (U : Opens X) (x : X) (hx : x ∈ U) :
    (additivePresheaf F).germ U x hx ≫ (stalkIso F x).hom =
      forgetToAdd.map (F.germ U x hx) :=
  ι_preservesColimitIso_inv forgetToAdd ((OpenNhds.inclusion x).op ⋙ F) (op ⟨U, hx⟩)

/-- The additive stalk of the forgotten ring presheaf is canonically the
underlying additive group of the actual ring-valued stalk. -/
def stalkAddEquiv (F : TopCat.Presheaf CommRingCat.{0} X) (x : X) :
    (additivePresheaf F).stalk x ≃+ F.stalk x :=
  (stalkIso F x).addCommGroupIsoToAddEquiv

/-- The canonical equivalence sends an actual additive germ to the
corresponding actual ring germ of the same section. -/
@[simp] theorem stalkAddEquiv_germ (F : TopCat.Presheaf CommRingCat.{0} X)
    (U : Opens X) (x : X) (hx : x ∈ U) (s : F.obj (op U)) :
    stalkAddEquiv F x ((additivePresheaf F).germ U x hx s) = F.germ U x hx s := by
  exact congrArg (fun k : (additivePresheaf F).obj (op U) ⟶
    forgetToAdd.obj (F.stalk x) => k s) (germ_stalkIso_hom F U x hx)

/-- The inverse canonical equivalence also preserves the actual
representatives; no choice of a section is introduced by this formula. -/
@[simp] theorem stalkAddEquiv_symm_germ (F : TopCat.Presheaf CommRingCat.{0} X)
    (U : Opens X) (x : X) (hx : x ∈ U) (s : F.obj (op U)) :
    (stalkAddEquiv F x).symm (F.germ U x hx s) =
      (additivePresheaf F).germ U x hx s := by
  apply (stalkAddEquiv F x).injective
  rw [AddEquiv.apply_symm_apply, stalkAddEquiv_germ]

end Wikipedia.HopfProblem.CuspNormalization.SheafForgetStalk
