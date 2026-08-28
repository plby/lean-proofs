import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupDerivationBasic

/-!
# Actual additive maps of the original ring skyscrapers

An additive map of coefficient rings acts on the underlying skyscrapers
through the original forgetful comparison. Evaluation over a containing
open is the original coefficient map. No multiplicativity of that map
is assumed.
-/

noncomputable section

open TopCat CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation

open SheafCupProduct CuspNormalization.SheafForgetStalk

attribute [local instance] Classical.propDecidable

variable {X : TopCat.{0}}

private theorem cast_map_eval {C : Type*} [Category C] {A₀ A B₀ B : C}
    (a : A₀ = A) (b : B₀ = B) (f : A ⟶ B) :
    (eqToHom a ≫ f ≫ eqToHom b.symm) ≫ eqToHom b = eqToHom a ≫ f := by
  simp

private theorem cast_unit_eval {C : Type*} [Category C] {A B₀ B : C}
    (b : B₀ = B) (f : A ⟶ B) :
    (f ≫ 𝟙 B ≫ eqToHom b.symm) ≫ eqToHom b = f := by
  simp

section Evaluation

variable {C : Type*} [Category C] [HasLimits C]

/-- The actual skyscraper section over a containing open is its original coefficient object. -/
def skyscraperAtIso (x : X) (A : C) (U : Opens X) (hx : x ∈ U) :
    (skyscraperSheaf x A).obj.obj (op U) ≅ A :=
  eqToIso (if_pos hx)

theorem skyscraperAtIso_map (x : X) {A B : C} (f : A ⟶ B)
    (U : Opens X) (hx : x ∈ U) :
    ((skyscraperSheafFunctor x).map f).hom.app (op U) ≫ (skyscraperAtIso x B U hx).hom =
      (skyscraperAtIso x A U hx).hom ≫ f := by
  have h : (SkyscraperPresheafFunctor.map' x f).app (op U) =
      eqToHom (if_pos hx) ≫ f ≫ eqToHom (if_pos hx).symm :=
    (SkyscraperPresheafFunctor.map'_app x f (op U)).trans (dif_pos hx)
  exact (congrArg (fun k => k ≫ (skyscraperAtIso x B U hx).hom) h).trans
    (cast_map_eval (if_pos hx) (if_pos hx) f)

/-- The original germ insertion evaluates to the actual original germ. -/
theorem skyscraperAtIso_unit [HasColimits C] (x : X) (F : TopCat.Sheaf C X)
    (U : Opens X) (hx : x ∈ U) :
    ((stalkSkyscraperSheafAdjunction x).unit.app F).hom.app (op U) ≫
        (skyscraperAtIso x (F.presheaf.stalk x) U hx).hom =
      F.presheaf.germ U x hx := by
  have h : (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x
      (𝟙 (F.presheaf.stalk x))).app (op U) =
        F.presheaf.germ U x hx ≫ 𝟙 _ ≫ eqToHom (if_pos hx).symm :=
    (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app
      x (𝟙 (F.presheaf.stalk x)) (op U)).trans (dif_pos hx)
  exact (congrArg (fun k => k ≫ (skyscraperAtIso x (F.presheaf.stalk x) U hx).hom) h).trans
    (cast_unit_eval (if_pos hx) (F.presheaf.germ U x hx))

end Evaluation

private theorem iso_trans_symm_hom_comp {C : Type*} [Category C] {A B E : C}
    (e : A ≅ E) (f : B ≅ E) : (e ≪≫ f.symm).hom ≫ f.hom = e.hom := by
  simp

/-- The genuine forgetful skyscraper comparison retains the original evaluation. -/
theorem skyscraperForget_eval (x : X) (A : CommRingCat.{0}) (U : Opens X) (hx : x ∈ U) :
    (GodementRing.skyscraperForgetIso x A).hom.hom.app (op U) ≫
        (skyscraperAtIso x (forgetToAdd.obj A) U hx).hom =
      forgetToAdd.map (skyscraperAtIso x A U hx).hom := by
  change (GodementRing.skyscraperForgetComponent x A (op U)).hom ≫
    (skyscraperAtIso x (forgetToAdd.obj A) U hx).hom = _
  simp only [GodementRing.skyscraperForgetComponent, dif_pos hx]
  exact iso_trans_symm_hom_comp
    (forgetToAdd.mapIso (skyscraperAtIso x A U hx))
    (skyscraperAtIso x (forgetToAdd.obj A) U hx)

/-- The original additive skyscraper functor acts on the actual underlying ring skyscrapers. -/
def skyscraperLift (x : X) {A B : CommRingCat.{0}} (f : A →+ B) :
    (GodementRing.forgetSheaf X).obj (skyscraperSheaf x A) ⟶
      (GodementRing.forgetSheaf X).obj (skyscraperSheaf x B) :=
  (GodementRing.skyscraperForgetIso x A).hom ≫
    (skyscraperSheafFunctor (C := AddCommGrpCat.{0}) x).map (AddCommGrpCat.ofHom f) ≫
      (GodementRing.skyscraperForgetIso x B).inv

private theorem inv_comp_of_hom_comp {C : Type*} [Category C] {A B E : C}
    (e : A ≅ B) (f : B ⟶ E) (g : A ⟶ E) (h : e.hom ≫ f = g) : e.inv ≫ g = f := by
  rw [← h, Iso.inv_hom_id_assoc]

private theorem comp_map_eval {C : Type*} [Category C] {A A' B' B E F : C}
    (a : A ⟶ A') (b : A' ⟶ B') (c : B' ⟶ B) (e : B ⟶ F) (d : B' ⟶ F)
    (k : A' ⟶ E) (l : A ⟶ E) (f : E ⟶ F)
    (hc : c ≫ e = d) (hb : b ≫ d = k ≫ f) (ha : a ≫ k = l) :
    (a ≫ b ≫ c) ≫ e = l ≫ f := by
  rw [Category.assoc, Category.assoc, hc, hb, ← Category.assoc, ha]

/-- The prolonged map is literally the coefficient map on every containing open. -/
theorem skyscraperLift_eval (x : X) {A B : CommRingCat.{0}} (f : A →+ B)
    (U : Opens X) (hx : x ∈ U) :
    (skyscraperLift x f).hom.app (op U) ≫
        forgetToAdd.map (skyscraperAtIso x B U hx).hom =
      forgetToAdd.map (skyscraperAtIso x A U hx).hom ≫ AddCommGrpCat.ofHom f := by
  let E := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op U)
  have hB : (GodementRing.skyscraperForgetIso x B).inv.hom.app (op U) ≫
      forgetToAdd.map (skyscraperAtIso x B U hx).hom =
        (skyscraperAtIso x (forgetToAdd.obj B) U hx).hom :=
    inv_comp_of_hom_comp (E.mapIso (GodementRing.skyscraperForgetIso x B))
      _ _ (skyscraperForget_eval x B U hx)
  exact comp_map_eval
    ((GodementRing.skyscraperForgetIso x A).hom.hom.app (op U))
    (((skyscraperSheafFunctor (C := AddCommGrpCat.{0}) x).map
      (AddCommGrpCat.ofHom f)).hom.app (op U))
    ((GodementRing.skyscraperForgetIso x B).inv.hom.app (op U))
    _ _ _ _ _ hB (skyscraperAtIso_map x (AddCommGrpCat.ofHom f) U hx)
    (skyscraperForget_eval x A U hx)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation
