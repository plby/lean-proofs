import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupDerivationGodementSections

/-!
# Naturality of the original germ inclusion for additive prolongation

Evaluation proves the unit identity for every actual underlying
additive map. The genuine functorial laws also prolong commuting
squares and actual zero composites.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation

open SheafCupProduct

variable {X : TopCat.{0}} {F G H K : GodementRing.RingSheaf X}

/-- The original ring germ inclusion is natural for the actual additive prolongation. -/
theorem liftMap_inclusion
    (f : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G) :
    (GodementRing.forgetSheaf X).map (GodementRing.inclusion F) ≫ liftMap f =
      f ≫ (GodementRing.forgetSheaf X).map (GodementRing.inclusion G) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply godementSection_ext G V.unop
  intro x hx
  exact ((evaluation_lift f V.unop x hx
    ((GodementRing.inclusion F).hom.app V a)).trans
      (congrArg (stalkMap f x) (evaluation_inclusion F V.unop x hx a))).trans
        ((stalkMap_germ f V.unop x hx a).trans
          (evaluation_inclusion G V.unop x hx (sectionMap f V.unop a)).symm)

theorem liftMap_square
    (f : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G)
    (g : (GodementRing.forgetSheaf X).obj G ⟶ (GodementRing.forgetSheaf X).obj K)
    (h : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj H)
    (k : (GodementRing.forgetSheaf X).obj H ⟶ (GodementRing.forgetSheaf X).obj K)
    (e : f ≫ g = h ≫ k) : liftMap f ≫ liftMap g = liftMap h ≫ liftMap k :=
  (liftMap_comp f g).symm.trans ((congrArg liftMap e).trans (liftMap_comp h k))

/-- Actual commuting additive operators continue to commute after prolongation. -/
theorem liftMap_commute (f g : End ((GodementRing.forgetSheaf X).obj F))
    (h : f ≫ g = g ≫ f) : liftMap f ≫ liftMap g = liftMap g ≫ liftMap f :=
  liftMap_square f g g f h

/-- Prolongation respects the original ring-functor image of an actual ring map. -/
theorem liftMap_ring_square (f : End ((GodementRing.forgetSheaf X).obj F))
    (g : End ((GodementRing.forgetSheaf X).obj G)) (r : F ⟶ G)
    (h : f ≫ (GodementRing.forgetSheaf X).map r =
      (GodementRing.forgetSheaf X).map r ≫ g) :
    liftMap f ≫ (GodementRing.forgetSheaf X).map (GodementRing.map r) =
      (GodementRing.forgetSheaf X).map (GodementRing.map r) ≫ liftMap g := by
  simpa only [liftMap_ring] using
    liftMap_square f ((GodementRing.forgetSheaf X).map r)
      ((GodementRing.forgetSheaf X).map r) g h

theorem liftMap_zero_comp
    (f : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G)
    (g : (GodementRing.forgetSheaf X).obj G ⟶ (GodementRing.forgetSheaf X).obj H)
    (h : f ≫ g = 0) : liftMap f ≫ liftMap g = 0 :=
  (liftMap_comp f g).symm.trans ((congrArg liftMap h).trans (liftMap_zero F H))

/-- A genuine ring inclusion killed by a derivation remains killed after prolongation. -/
theorem lifted_ring_annihilate (r : F ⟶ G) (D : SheafDerivation G)
    (h : (GodementRing.forgetSheaf X).map r ≫ D.map = 0) :
    (GodementRing.forgetSheaf X).map (GodementRing.map r) ≫ (liftedDerivation D).map = 0 := by
  simpa only [liftMap_ring, liftedDerivation_map] using
    liftMap_zero_comp ((GodementRing.forgetSheaf X).map r) D.map h

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation
