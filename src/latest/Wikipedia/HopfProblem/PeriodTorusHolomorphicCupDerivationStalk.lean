import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupDerivationBasic

/-!
# Actual additive maps and derivations on the original ring stalks

The additive stalk map is transported by the proved forgetful-stalk
comparison. Its value on a germ is the germ of the original section
map. The Leibniz rule follows after restricting two representatives to
one actual common neighbourhood.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation

open SheafCupProduct CuspNormalization.SheafForgetStalk

variable {X : TopCat.{0}} {F G H : GodementRing.RingSheaf X}

/-- The original additive stalk map on the underlying original ring stalks. -/
def stalkMap
    (f : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G)
    (x : X) : F.presheaf.stalk x →+ G.presheaf.stalk x :=
  (stalkAddEquiv G.presheaf x).toAddMonoidHom.comp
    (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.hom).hom.comp
      (stalkAddEquiv F.presheaf x).symm.toAddMonoidHom)

/-- Prolongation retains the literal original germ formula. -/
theorem stalkMap_germ
    (f : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G)
    (U : Opens X) (x : X) (hx : x ∈ U) (a : F.obj.obj (op U)) :
    stalkMap f x (F.presheaf.germ U x hx a) =
      G.presheaf.germ U x hx (sectionMap f U a) := by
  change stalkAddEquiv G.presheaf x
    (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map f.hom)
      ((stalkAddEquiv F.presheaf x).symm (F.presheaf.germ U x hx a))) = _
  rw [stalkAddEquiv_symm_germ]
  exact (congrArg (stalkAddEquiv G.presheaf x)
    (TopCat.Presheaf.stalkFunctor_map_germ_apply
      (F := additivePresheaf F.presheaf) (G := additivePresheaf G.presheaf)
      U x hx f.hom a)).trans
    (stalkAddEquiv_germ G.presheaf U x hx (sectionMap f U a))

theorem stalkMap_id (F : GodementRing.RingSheaf X) (x : X) :
    stalkMap (𝟙 ((GodementRing.forgetSheaf X).obj F)) x = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨U, hx, a, rfl⟩ := F.presheaf.exists_germ_eq a
  rw [stalkMap_germ]
  rfl

theorem stalkMap_comp
    (f : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G)
    (g : (GodementRing.forgetSheaf X).obj G ⟶ (GodementRing.forgetSheaf X).obj H) (x : X) :
    stalkMap (f ≫ g) x = (stalkMap g x).comp (stalkMap f x) := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨U, hx, a, rfl⟩ := F.presheaf.exists_germ_eq a
  rw [stalkMap_germ, AddMonoidHom.comp_apply, stalkMap_germ, stalkMap_germ]
  rfl

theorem stalkMap_zero (F G : GodementRing.RingSheaf X) (x : X) :
    stalkMap (0 : (GodementRing.forgetSheaf X).obj F ⟶
      (GodementRing.forgetSheaf X).obj G) x = 0 := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨U, hx, a, rfl⟩ := F.presheaf.exists_germ_eq a
  rw [stalkMap_germ]
  change G.presheaf.germ U x hx 0 = 0
  exact map_zero _

theorem stalkMap_add
    (f g : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G)
    (x : X) : stalkMap (f + g) x = stalkMap f x + stalkMap g x := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨U, hx, a, rfl⟩ := F.presheaf.exists_germ_eq a
  rw [stalkMap_germ, AddMonoidHom.add_apply, stalkMap_germ, stalkMap_germ]
  exact (G.presheaf.germ U x hx).hom.map_add (sectionMap f U a) (sectionMap g U a)

/-- A genuine ring map gives the original ring-stalk map, after forgetting multiplication. -/
theorem stalkMap_ring (f : F ⟶ G) (x : X) :
    stalkMap ((GodementRing.forgetSheaf X).map f) x =
      ((GodementRing.stalk x).map f).hom.toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨U, hx, a, rfl⟩ := F.presheaf.exists_germ_eq a
  rw [stalkMap_germ]
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx f.hom a).symm

/-- The prolonged operator satisfies Leibniz in the actual original ring stalk. -/
theorem stalkMap_mul (D : SheafDerivation F) (x : X) (a b : F.presheaf.stalk x) :
    stalkMap D.map x (a * b) = stalkMap D.map x a * b + a * stalkMap D.map x b := by
  obtain ⟨U, hxU, a, rfl⟩ := F.presheaf.exists_germ_eq a
  obtain ⟨V, hVU, hxV, b, rfl⟩ := F.presheaf.exists_le_germ_eq b hxU
  rw [← F.presheaf.germ_res_apply (homOfLE hVU) x hxV a]
  rw [← map_mul, stalkMap_germ, D.leibniz, map_add, map_mul, map_mul,
    stalkMap_germ, stalkMap_germ]

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation
