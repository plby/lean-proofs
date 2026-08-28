import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafForgetStalkBasic

/-!
# Stalks of the actual additive constant complex sheaf

The forgetful functor from commutative rings to additive groups preserves
filtered colimits.  Its proved comparison on actual stalks, followed by
the constant ring-sheaf stalk isomorphism, identifies the actual additive
stalk with `ℂ`.  The identification preserves the germs of the actual
sheafification-unit sections.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory TopCat

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

/-- The additive constant-sheaf stalk is canonically `ℂ`, using the
actual filtered-colimit comparison and the actual ring-sheaf stalk. -/
def complexAdditiveSheafStalkIso (X : TopCat.{0}) (x : X) :
    Presheaf.stalk (C := AddCommGrpCat) (complexAdditiveSheaf X).obj x ≅
      AddCommGrpCat.of ℂ :=
  SheafForgetStalk.stalkIso (complexSheaf X).obj x ≪≫
    SheafForgetStalk.forgetToAdd.mapIso (complexSheafStalkIso X x)

/-- The same canonical identification as an additive equivalence. -/
def complexAdditiveSheafStalkEquiv (X : TopCat.{0}) (x : X) :
    Presheaf.stalk (C := AddCommGrpCat) (complexAdditiveSheaf X).obj x ≃+ ℂ :=
  (complexAdditiveSheafStalkIso X x).addCommGroupIsoToAddEquiv

/-- The additive identification factors through the independently proved
forgetful comparison of actual stalks. -/
theorem complexAdditiveSheafStalkEquiv_apply (X : TopCat.{0}) (x : X)
    (s : Presheaf.stalk (C := AddCommGrpCat) (complexAdditiveSheaf X).obj x) :
    complexAdditiveSheafStalkEquiv X x s =
      complexSheafStalkEquiv X x (SheafForgetStalk.stalkAddEquiv (complexSheaf X).obj x s) :=
  rfl

/-- A germ of the actual additive constant section maps to its original
complex value. -/
@[simp] theorem complexAdditiveSheafStalkEquiv_germ_unit (X : TopCat.{0}) (x : X)
    (U : Opens X) (hx : x ∈ U) (c : ℂ) :
    complexAdditiveSheafStalkEquiv X x
      (Presheaf.germ (complexAdditiveSheaf X).obj U x hx
        ((additiveUnit X).app (op U) c)) = c := by
  exact (congrArg (complexSheafStalkEquiv X x)
    (SheafForgetStalk.stalkAddEquiv_germ (complexSheaf X).obj U x hx
      ((unit X).app (op U) c))).trans
    (complexSheafStalkEquiv_germ_unit X x U hx c)

/-- The identification commutes with the actual additive unit and germ
maps as an equality in the category of additive groups. -/
@[reassoc (attr := simp)]
theorem additiveUnit_germ_complexAdditiveSheafStalkIso_hom
    (X : TopCat.{0}) (x : X) (U : Opens X) (hx : x ∈ U) :
    (additiveUnit X).app (op U) ≫ Presheaf.germ (complexAdditiveSheaf X).obj U x hx ≫
      (complexAdditiveSheafStalkIso X x).hom = 𝟙 (AddCommGrpCat.of ℂ) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  exact complexAdditiveSheafStalkEquiv_germ_unit X x U hx c

/-- The inverse equivalence is represented by the actual constant
section on any chosen open neighbourhood. -/
theorem complexAdditiveSheafStalkEquiv_symm_eq_germ_unit
    (X : TopCat.{0}) (x : X) (U : Opens X) (hx : x ∈ U) (c : ℂ) :
    (complexAdditiveSheafStalkEquiv X x).symm c =
      Presheaf.germ (complexAdditiveSheaf X).obj U x hx
        ((additiveUnit X).app (op U) c) := by
  apply (complexAdditiveSheafStalkEquiv X x).injective
  exact ((complexAdditiveSheafStalkEquiv X x).apply_symm_apply c).trans
    (complexAdditiveSheafStalkEquiv_germ_unit X x U hx c).symm

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
