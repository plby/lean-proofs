import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupDerivationSkyscraper

/-!
# Functoriality of the actual additive skyscraper lifts

The original additive skyscraper functor supplies composition, zero,
and addition. Agreement with a genuine ring map follows by evaluation
on containing opens and the actual terminal object on the remaining opens.
-/

noncomputable section

open TopCat CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation

open SheafCupProduct CuspNormalization.SheafForgetStalk

attribute [local instance] Classical.propDecidable

variable {X : TopCat.{0}}

private theorem transport_id {C : Type*} [Category C] {A B : C}
    (e : A ≅ B) (u : B ⟶ B) (hu : u = 𝟙 B) : e.hom ≫ u ≫ e.inv = 𝟙 A := by
  rw [hu]
  simp

private theorem transport_comp {C : Type*} [Category C] {A A' B B' E E' : C}
    (eA : A ≅ A') (eB : B ≅ B') (eE : E ≅ E')
    (f : A' ⟶ B') (g : B' ⟶ E') (u : A' ⟶ E') (hu : u = f ≫ g) :
    eA.hom ≫ u ≫ eE.inv = (eA.hom ≫ f ≫ eB.inv) ≫ (eB.hom ≫ g ≫ eE.inv) := by
  rw [hu]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem transport_zero {C : Type*} [Category C] [Preadditive C]
    {A A' B B' : C} (eA : A ≅ A') (eB : B ≅ B') (u : A' ⟶ B') (hu : u = 0) :
    eA.hom ≫ u ≫ eB.inv = 0 := by
  rw [hu]
  simp

private theorem transport_add {C : Type*} [Category C] [Preadditive C]
    {A A' B B' : C} (eA : A ≅ A') (eB : B ≅ B')
    (f g u : A' ⟶ B') (hu : u = f + g) :
    eA.hom ≫ u ≫ eB.inv = (eA.hom ≫ f ≫ eB.inv) + (eA.hom ≫ g ≫ eB.inv) := by
  rw [hu]
  simp only [Preadditive.comp_add, Preadditive.add_comp]

theorem skyscraperLift_id (x : X) (A : CommRingCat.{0}) :
    skyscraperLift x (AddMonoidHom.id A) = 𝟙 _ :=
  transport_id (GodementRing.skyscraperForgetIso x A) _
    ((skyscraperSheafFunctor (C := AddCommGrpCat.{0}) x).map_id (forgetToAdd.obj A))

theorem skyscraperLift_comp (x : X) {A B C : CommRingCat.{0}}
    (f : A →+ B) (g : B →+ C) :
    skyscraperLift x (g.comp f) = skyscraperLift x f ≫ skyscraperLift x g :=
  transport_comp (GodementRing.skyscraperForgetIso x A)
    (GodementRing.skyscraperForgetIso x B) (GodementRing.skyscraperForgetIso x C)
    _ _ _ ((skyscraperSheafFunctor (C := AddCommGrpCat.{0}) x).map_comp
      (AddCommGrpCat.ofHom f) (AddCommGrpCat.ofHom g))

theorem skyscraperLift_zero (x : X) (A B : CommRingCat.{0}) :
    skyscraperLift x (0 : A →+ B) = 0 :=
  transport_zero (GodementRing.skyscraperForgetIso x A)
    (GodementRing.skyscraperForgetIso x B) _
    ((skyscraperSheafFunctor (C := AddCommGrpCat.{0}) x).map_zero _ _)

theorem skyscraperLift_add (x : X) {A B : CommRingCat.{0}} (f g : A →+ B) :
    skyscraperLift x (f + g) = skyscraperLift x f + skyscraperLift x g :=
  transport_add (GodementRing.skyscraperForgetIso x A)
    (GodementRing.skyscraperForgetIso x B) _ _ _
    ((skyscraperSheafFunctor (C := AddCommGrpCat.{0}) x).map_add
      (f := AddCommGrpCat.ofHom f) (g := AddCommGrpCat.ofHom g))

/-- Actual maps into a forgotten ring skyscraper are determined on containing opens. -/
theorem skyscraper_map_ext (x : X) (A : CommRingCat.{0})
    {M : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f g : M ⟶ (GodementRing.forgetSheaf X).obj (skyscraperSheaf x A))
    (h : ∀ (U : Opens X) (hx : x ∈ U),
      f.hom.app (op U) ≫ forgetToAdd.map (skyscraperAtIso x A U hx).hom =
        g.hom.app (op U) ≫ forgetToAdd.map (skyscraperAtIso x A U hx).hom) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  by_cases hx : x ∈ V.unop
  · exact (cancel_mono (forgetToAdd.map (skyscraperAtIso x A V.unop hx).hom)).mp (h V.unop hx)
  · have ht : IsTerminal
        (((GodementRing.forgetSheaf X).obj (skyscraperSheaf x A)).obj.obj V) := by
      change IsTerminal (forgetToAdd.obj (if x ∈ V.unop then A else terminal CommRingCat))
      rw [if_neg hx]
      exact isLimitOfHasTerminalOfPreservesLimit forgetToAdd
    exact ht.hom_ext _ _

/-- On genuine ring maps this is exactly the original forgotten ring-skyscraper map. -/
theorem skyscraperLift_ring (x : X) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    skyscraperLift x f.hom.toAddMonoidHom =
      (GodementRing.forgetSheaf X).map ((skyscraperSheafFunctor x).map f) := by
  apply skyscraper_map_ext x B
  intro U hx
  have h := (forgetToAdd.map_comp _ _).symm.trans
    ((congrArg forgetToAdd.map (skyscraperAtIso_map x f U hx)).trans
      (forgetToAdd.map_comp _ _))
  exact (skyscraperLift_eval x f.hom.toAddMonoidHom U hx).trans h.symm

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation
