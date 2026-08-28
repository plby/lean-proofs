import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Actual additive-functor images of binary total terms

The comparison with a literal pair is the canonical finite-biproduct
comparison, not a chosen identification of cohomology. Its two
coordinates are precisely the images of the original projections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalCategory

universe v u w

@[reassoc] theorem biprodIsoProd_hom_fst (A B : AddCommGrpCat.{w}) :
    (AddCommGrpCat.biprodIsoProd A B).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst A B) = biprod.fst := by
  apply (cancel_epi (AddCommGrpCat.biprodIsoProd A B).inv).mp
  simp only [Iso.inv_hom_id_assoc, AddCommGrpCat.biprodIsoProd_inv_comp_fst]

@[reassoc] theorem biprodIsoProd_hom_snd (A B : AddCommGrpCat.{w}) :
    (AddCommGrpCat.biprodIsoProd A B).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd A B) = biprod.snd := by
  apply (cancel_epi (AddCommGrpCat.biprodIsoProd A B).inv).mp
  simp only [Iso.inv_hom_id_assoc, AddCommGrpCat.biprodIsoProd_inv_comp_snd]

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] (A B : C)

local instance : PreservesBinaryBiproducts F :=
  preservesBinaryBiproducts_of_preservesBiproducts F

/-- The actual image of a binary categorical biproduct, as a pair. -/
def binaryIso : F.obj (A ⊞ B) ≅ AddCommGrpCat.of (F.obj A × F.obj B) :=
  F.mapBiprod A B ≪≫ AddCommGrpCat.biprodIsoProd (F.obj A) (F.obj B)

def binaryEquiv : F.obj (A ⊞ B) ≃+ (F.obj A × F.obj B) :=
  (binaryIso F A B).addCommGroupIsoToAddEquiv

@[reassoc] theorem binaryIso_hom_fst :
    (binaryIso F A B).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst (F.obj A) (F.obj B)) =
      F.map biprod.fst := by
  simp only [binaryIso, Iso.trans_hom, Category.assoc, biprodIsoProd_hom_fst,
    Functor.mapBiprod_hom, biprod.lift_fst]

@[reassoc] theorem binaryIso_hom_snd :
    (binaryIso F A B).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd (F.obj A) (F.obj B)) =
      F.map biprod.snd := by
  simp only [binaryIso, Iso.trans_hom, Category.assoc, biprodIsoProd_hom_snd,
    Functor.mapBiprod_hom, biprod.lift_snd]

@[simp] theorem binaryEquiv_fst (s : F.obj (A ⊞ B)) :
    (binaryEquiv F A B s).1 = F.map biprod.fst s :=
  ConcreteCategory.congr_hom (binaryIso_hom_fst F A B) s

@[simp] theorem binaryEquiv_snd (s : F.obj (A ⊞ B)) :
    (binaryEquiv F A B s).2 = F.map biprod.snd s :=
  ConcreteCategory.congr_hom (binaryIso_hom_snd F A B) s

theorem binaryEquiv_apply (s : F.obj (A ⊞ B)) :
    binaryEquiv F A B s = (F.map biprod.fst s, F.map biprod.snd s) :=
  Prod.ext (binaryEquiv_fst F A B s) (binaryEquiv_snd F A B s)

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalCategory
