import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsBasic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Stalks of the actual constant complex sheaf

The constant-presheaf stalk is the colimit of the genuinely constant
diagram over the connected category of open neighbourhoods.  The unit
of sheafification is an isomorphism on stalks, so it gives a canonical
identification of the actual constant-sheaf stalk with `ℂ` on every
small topological space, without a local-connectedness hypothesis.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory Limits TopCat

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

/-- The actual colimit stalk of the constant complex presheaf is `ℂ`. -/
def constantPresheafStalkIso (X : TopCat.{0}) (x : X) :
    (constantPresheaf X).stalk x ≅ CommRingCat.of ℂ := by
  letI : IsConnected (OpenNhds x)ᵒᵖ := IsFiltered.isConnected _
  exact IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ constantPresheaf X))
    (isColimitConstCocone (OpenNhds x)ᵒᵖ (CommRingCat.of ℂ))

/-- Every constant-presheaf germ has its original value under the stalk
isomorphism. -/
@[reassoc (attr := simp)]
theorem constantPresheaf_germ_stalkIso_hom (X : TopCat.{0}) (x : X)
    (U : Opens X) (hx : x ∈ U) :
    (constantPresheaf X).germ U x hx ≫ (constantPresheafStalkIso X x).hom =
      𝟙 (CommRingCat.of ℂ) := by
  have : IsConnected (OpenNhds x)ᵒᵖ := IsFiltered.isConnected _
  exact colimit.comp_coconePointUniqueUpToIso_hom
    (F := (OpenNhds.inclusion x).op ⋙ constantPresheaf X)
    (isColimitConstCocone (OpenNhds x)ᵒᵖ (CommRingCat.of ℂ))
    (op (⟨U, hx⟩ : OpenNhds x))

/-- Sheafification preserves the actual stalk of the constant presheaf. -/
instance unit_stalk_isIso (X : TopCat.{0}) (x : X) :
    IsIso ((Presheaf.stalkFunctor CommRingCat x).map (unit X)) :=
  Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat (constantPresheaf X)

/-- The canonical identification of the actual constant-sheaf stalk with
the complex numbers. -/
def complexSheafStalkIso (X : TopCat.{0}) (x : X) :
    Presheaf.stalk (C := CommRingCat) (complexSheaf X).obj x ≅ CommRingCat.of ℂ :=
  (asIso ((Presheaf.stalkFunctor CommRingCat x).map (unit X))).symm ≪≫
    constantPresheafStalkIso X x

/-- The stalk identifications commute with the sheafification unit. -/
@[reassoc (attr := simp)]
theorem unit_stalk_complexSheafStalkIso_hom (X : TopCat.{0}) (x : X) :
    (Presheaf.stalkFunctor CommRingCat x).map (unit X) ≫
      (complexSheafStalkIso X x).hom = (constantPresheafStalkIso X x).hom := by
  change (Presheaf.stalkFunctor CommRingCat x).map (unit X) ≫
    inv ((Presheaf.stalkFunctor CommRingCat x).map (unit X)) ≫
      (constantPresheafStalkIso X x).hom = _
  exact IsIso.hom_inv_id_assoc _ _

/-- The germ of a sheafified constant section retains its actual value. -/
@[reassoc (attr := simp)]
theorem unit_germ_complexSheafStalkIso_hom (X : TopCat.{0}) (x : X)
    (U : Opens X) (hx : x ∈ U) :
    (unit X).app (op U) ≫ Presheaf.germ (complexSheaf X).obj U x hx ≫
      (complexSheafStalkIso X x).hom = 𝟙 (CommRingCat.of ℂ) := by
  exact (Presheaf.stalkFunctor_map_germ_assoc U x hx (unit X)
    (complexSheafStalkIso X x).hom).symm.trans
      ((congrArg (fun f => (constantPresheaf X).germ U x hx ≫ f)
        (unit_stalk_complexSheafStalkIso_hom X x)).trans
          (constantPresheaf_germ_stalkIso_hom X x U hx))

/-- The constant-presheaf stalk identification as an actual ring equivalence. -/
def constantPresheafStalkEquiv (X : TopCat.{0}) (x : X) :
    (constantPresheaf X).stalk x ≃+* ℂ :=
  (constantPresheafStalkIso X x).commRingCatIsoToRingEquiv

/-- The constant-sheaf stalk identification as an actual ring equivalence. -/
def complexSheafStalkEquiv (X : TopCat.{0}) (x : X) :
    Presheaf.stalk (C := CommRingCat) (complexSheaf X).obj x ≃+* ℂ :=
  (complexSheafStalkIso X x).commRingCatIsoToRingEquiv

@[simp] theorem constantPresheafStalkEquiv_germ (X : TopCat.{0}) (x : X)
    (U : Opens X) (hx : x ∈ U) (c : ℂ) :
    constantPresheafStalkEquiv X x ((constantPresheaf X).germ U x hx c) = c :=
  ConcreteCategory.congr_hom (constantPresheaf_germ_stalkIso_hom X x U hx) c

@[simp] theorem complexSheafStalkEquiv_germ_unit (X : TopCat.{0}) (x : X)
    (U : Opens X) (hx : x ∈ U) (c : ℂ) :
    complexSheafStalkEquiv X x
      (Presheaf.germ (complexSheaf X).obj U x hx ((unit X).app (op U) c)) = c :=
  ConcreteCategory.congr_hom (unit_germ_complexSheafStalkIso_hom X x U hx) c

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
