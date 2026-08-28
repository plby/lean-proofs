import Wikipedia.HopfProblem.SheafCupProductGodementRing
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Forgetting the ring structure in the actual Godement construction

The forgetful functor on sheaves preserves actual small limits.  It also
identifies the underlying additive sheaf of a ring skyscraper with the
genuine additive skyscraper of the same coefficient group.  The latter
comparison uses the actual terminal-object comparison on opens which do
not contain the point.
-/

noncomputable section

open TopCat TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.SheafCupProduct.GodementRing

open CuspNormalization.SheafForgetStalk

attribute [local instance] Classical.propDecidable

/-- The existing ring-to-additive sheaf functor. -/
abbrev forgetSheaf (X : TopCat.{0}) : RingSheaf X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X :=
  sheafCompose (Opens.grothendieckTopology X) forgetToAdd

instance forgetSheaf_preservesLimits (X : TopCat.{0}) :
    PreservesLimitsOfSize.{0, 0} (forgetSheaf X) := by
  let : PreservesLimitsOfSize.{0, 0} (TopCat.Sheaf.forget CommRingCat.{0} X) :=
    (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X)
      CommRingCat.{0}).rightAdjoint_preservesLimits
  have : PreservesLimitsOfSize.{0, 0}
      ((Functor.whiskeringRight (Opens X)ᵒᵖ CommRingCat.{0} AddCommGrpCat.{0}).obj
        forgetToAdd) := by infer_instance
  let : PreservesLimitsOfSize.{0, 0}
      (forgetSheaf X ⋙ TopCat.Sheaf.forget AddCommGrpCat.{0} X) :=
    inferInstanceAs (PreservesLimitsOfSize.{0, 0}
      (TopCat.Sheaf.forget CommRingCat.{0} X ⋙
        (Functor.whiskeringRight (Opens X)ᵒᵖ CommRingCat.{0} AddCommGrpCat.{0}).obj
          forgetToAdd))
  exact preservesLimits_of_reflects_of_preserves (forgetSheaf X)
    (TopCat.Sheaf.forget AddCommGrpCat.{0} X)

variable {X : TopCat.{0}}

private theorem transportedSquare {A₀ A₁ A : CommRingCat.{0}}
    {B₀ B₁ : AddCommGrpCat.{0}} (a₀ : A₀ = A) (a₁ : A₁ = A)
    (b₀ : B₀ = forgetToAdd.obj A) (b₁ : B₁ = forgetToAdd.obj A)
    (eA : A₀ = A₁) (eB : B₀ = B₁) :
    forgetToAdd.map (eqToHom eA) ≫
        (forgetToAdd.mapIso (eqToIso a₁) ≪≫ (eqToIso b₁).symm).hom =
      (forgetToAdd.mapIso (eqToIso a₀) ≪≫ (eqToIso b₀).symm).hom ≫ eqToHom eB := by
  subst A₀ A₁ B₀ B₁
  simp

/-- The original coefficient group over a containing open, and the
canonical terminal comparison over every other open. -/
def skyscraperForgetComponent (x : X) (A : CommRingCat.{0}) (V : (Opens X)ᵒᵖ) :
    ((forgetSheaf X).obj (skyscraperSheaf x A)).obj.obj V ≅
      (skyscraperSheaf x (forgetToAdd.obj A)).obj.obj V := by
  change forgetToAdd.obj (if x ∈ V.unop then A else terminal CommRingCat) ≅
    (if x ∈ V.unop then forgetToAdd.obj A else terminal AddCommGrpCat)
  by_cases h : x ∈ V.unop
  · exact forgetToAdd.mapIso (eqToIso (if_pos h)) ≪≫ (eqToIso (if_pos h)).symm
  · exact forgetToAdd.mapIso (eqToIso (if_neg h)) ≪≫ PreservesTerminal.iso forgetToAdd ≪≫
      (eqToIso (if_neg h)).symm

theorem skyscraperForgetComponent_naturality (x : X) (A : CommRingCat.{0})
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ((forgetSheaf X).obj (skyscraperSheaf x A)).obj.map i ≫
        (skyscraperForgetComponent x A V).hom =
      (skyscraperForgetComponent x A U).hom ≫
        (skyscraperSheaf x (forgetToAdd.obj A)).obj.map i := by
  by_cases hV : x ∈ V.unop
  · have hU : x ∈ U.unop := leOfHom i.unop hV
    change forgetToAdd.map ((skyscraperPresheaf x A).map i) ≫
      (skyscraperForgetComponent x A V).hom =
      (skyscraperForgetComponent x A U).hom ≫
        (skyscraperPresheaf x (forgetToAdd.obj A)).map i
    simp only [Functor.comp_obj, skyscraperPresheaf_map, skyscraperForgetComponent,
      dif_pos hU, dif_pos hV]
    exact transportedSquare _ _ _ _ _ _
  · have ht : IsTerminal ((skyscraperSheaf x (forgetToAdd.obj A)).obj.obj V) := by
      change IsTerminal (if x ∈ V.unop then forgetToAdd.obj A else terminal AddCommGrpCat)
      rw [if_neg hV]
      exact terminalIsTerminal
    exact ht.hom_ext _ _

/-- A canonical actual presheaf comparison, including all restriction maps. -/
def skyscraperForgetPresheafIso (x : X) (A : CommRingCat.{0}) :
    ((forgetSheaf X).obj (skyscraperSheaf x A)).obj ≅
      (skyscraperSheaf x (forgetToAdd.obj A)).obj :=
  NatIso.ofComponents (skyscraperForgetComponent x A)
    (fun i => skyscraperForgetComponent_naturality x A i)

/-- The forgotten ring skyscraper is the genuine additive skyscraper. -/
def skyscraperForgetIso (x : X) (A : CommRingCat.{0}) :
    (forgetSheaf X).obj (skyscraperSheaf x A) ≅
      skyscraperSheaf x (forgetToAdd.obj A) where
  hom := ⟨(skyscraperForgetPresheafIso x A).hom⟩
  inv := ⟨(skyscraperForgetPresheafIso x A).inv⟩
  hom_inv_id := CategoryTheory.Sheaf.hom_ext (skyscraperForgetPresheafIso x A).hom_inv_id
  inv_hom_id := CategoryTheory.Sheaf.hom_ext (skyscraperForgetPresheafIso x A).inv_hom_id

end Wikipedia.HopfProblem.SheafCupProduct.GodementRing
