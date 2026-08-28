import Wikipedia.HopfProblem.SheafCupProductGodementExactBasic

/-!
# Retraction on the genuine additive stalks

The actual ring-stalk evaluation is transported through the proved
forgetful-stalk comparison. It retracts the actual additive augmentation
and remains natural for every original ring-sheaf morphism.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafCupProduct.GodementExact

open GodementRing
open CuspNormalization.SheafForgetStalk (forgetToAdd)

variable {X : TopCat.{0}}

/-- The actual additive stalk functor on sheaves. -/
abbrev additiveStalk (x : X) := CuspNormalization.SheafBiproduct.stalkFunctor X x

/-- The canonical comparison with the underlying group of the ring stalk. -/
def stalkComparison (F : RingSheaf X) (x : X) :
    (additiveStalk x).obj (additiveSheaf F) ≅ forgetToAdd.obj ((stalk x).obj F) :=
  CuspNormalization.SheafForgetStalk.stalkIso F.presheaf x

@[reassoc] theorem stalkComparison_naturality {F G : RingSheaf X} (f : F ⟶ G)
    (x : X) :
    (additiveStalk x).map ((forgetSheaf X).map f) ≫ (stalkComparison G x).hom =
      (stalkComparison F x).hom ≫ forgetToAdd.map ((stalk x).map f) :=
  CuspNormalization.SheafForgetStalk.stalkIso_naturality f.hom x

/-- Evaluation at the same point on the genuine additive stalk. -/
def stalkRetraction (F : RingSheaf X) (x : X) :
    (additiveStalk x).obj (I0 F) ⟶ (additiveStalk x).obj (additiveSheaf F) :=
  (stalkComparison (sheaf F) x).hom ≫ forgetToAdd.map (retraction F x) ≫
    (stalkComparison F x).inv

@[reassoc] theorem stalkRetraction_comparison (F : RingSheaf X) (x : X) :
    stalkRetraction F x ≫ (stalkComparison F x).hom =
      (stalkComparison (sheaf F) x).hom ≫ forgetToAdd.map (retraction F x) := by
  simp only [stalkRetraction, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The genuine augmentation is split injective on every stalk. -/
@[reassoc] theorem augmentation_stalkRetraction (F : RingSheaf X) (x : X) :
    (additiveStalk x).map (augmentation F) ≫ stalkRetraction F x =
      𝟙 ((additiveStalk x).obj (additiveSheaf F)) := by
  apply (cancel_mono (stalkComparison F x).hom).mp
  change ((additiveStalk x).map ((forgetSheaf X).map (inclusion F)) ≫
    stalkRetraction F x) ≫ (stalkComparison F x).hom = _
  rw [Category.assoc, stalkRetraction_comparison, ← Category.assoc,
    stalkComparison_naturality (inclusion F) x, Category.assoc,
    ← Functor.map_comp, inclusion_retraction, forgetToAdd.map_id, Category.comp_id,
    Category.id_comp]

/-- Naturality survives transport to the actual forgotten stalks. -/
@[reassoc] theorem stalkRetraction_naturality {F G : RingSheaf X} (f : F ⟶ G)
    (x : X) :
    (additiveStalk x).map ((forgetSheaf X).map (map f)) ≫ stalkRetraction G x =
      stalkRetraction F x ≫ (additiveStalk x).map ((forgetSheaf X).map f) := by
  apply (cancel_mono (stalkComparison G x).hom).mp
  calc
    ((additiveStalk x).map ((forgetSheaf X).map (map f)) ≫ stalkRetraction G x) ≫
        (stalkComparison G x).hom =
      ((stalkComparison (sheaf F) x).hom ≫ forgetToAdd.map (retraction F x)) ≫
        forgetToAdd.map ((stalk x).map f) := by
      rw [Category.assoc, stalkRetraction_comparison, ← Category.assoc,
        stalkComparison_naturality (map f) x, Category.assoc,
        ← Functor.map_comp, retraction_naturality, Functor.map_comp, Category.assoc]
    _ = (stalkRetraction F x ≫ (stalkComparison F x).hom) ≫
        forgetToAdd.map ((stalk x).map f) := by rw [stalkRetraction_comparison]
    _ = (stalkRetraction F x ≫ (additiveStalk x).map ((forgetSheaf X).map f)) ≫
        (stalkComparison G x).hom := by
      rw [Category.assoc, Category.assoc, stalkComparison_naturality f x]

end Wikipedia.HopfProblem.SheafCupProduct.GodementExact
