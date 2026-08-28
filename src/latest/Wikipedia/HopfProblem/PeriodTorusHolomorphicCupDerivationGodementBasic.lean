import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupDerivationStalk
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupDerivationSkyscraperMaps

/-!
# Actual additive prolongation to multiplicative Godement terms

The forgotten original ring product is an actual product of the
forgotten original ring skyscrapers. Its universal property prolongs
every underlying additive sheaf map by the actual stalk maps.
-/

noncomputable section

open TopCat CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation

open SheafCupProduct

attribute [local instance] Classical.propDecidable

variable {X : TopCat.{0}} {F G H : GodementRing.RingSheaf X}

/-- The actual map on each original forgotten ring skyscraper. -/
def pointLift
    (f : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G)
    (x : X) :
    (GodementRing.forgetSheaf X).obj (GodementRing.pointTerm F x) ⟶
      (GodementRing.forgetSheaf X).obj (GodementRing.pointTerm G x) :=
  skyscraperLift x (stalkMap f x)

theorem pointLift_comp
    (f : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G)
    (g : (GodementRing.forgetSheaf X).obj G ⟶ (GodementRing.forgetSheaf X).obj H) (x : X) :
    pointLift (f ≫ g) x = pointLift f x ≫ pointLift g x := by
  rw [pointLift, stalkMap_comp, skyscraperLift_comp]
  rfl

theorem pointLift_ring (f : F ⟶ G) (x : X) :
    pointLift ((GodementRing.forgetSheaf X).map f) x =
      (GodementRing.forgetSheaf X).map (GodementRing.pointMap f x) :=
  (congrArg (skyscraperLift x) (stalkMap_ring f x)).trans
    (skyscraperLift_ring x ((GodementRing.stalk x).map f))

/-- The actual forgotten multiplicative product retains its original limit property. -/
def forgottenProductIsLimit (F : GodementRing.RingSheaf X) :
    IsLimit (Fan.mk ((GodementRing.forgetSheaf X).obj (GodementRing.sheaf F))
      (fun x => (GodementRing.forgetSheaf X).map (Pi.π (GodementRing.pointTerm F) x))) :=
  isLimitOfHasProductOfPreservesLimit (GodementRing.forgetSheaf X) (GodementRing.pointTerm F)

/-- Maps into the actual forgotten Godement term are determined by its actual projections. -/
theorem godement_map_ext (F : GodementRing.RingSheaf X)
    {M : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f g : M ⟶ (GodementRing.forgetSheaf X).obj (GodementRing.sheaf F))
    (h : ∀ x, f ≫ (GodementRing.forgetSheaf X).map (Pi.π (GodementRing.pointTerm F) x) =
      g ≫ (GodementRing.forgetSheaf X).map (Pi.π (GodementRing.pointTerm F) x)) : f = g := by
  apply (forgottenProductIsLimit F).hom_ext
  intro x
  exact h x.as

/-- Actual additive prolongation on the underlying original multiplicative Godement terms. -/
def liftMap
    (f : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G) :
    (GodementRing.forgetSheaf X).obj (GodementRing.sheaf F) ⟶
      (GodementRing.forgetSheaf X).obj (GodementRing.sheaf G) :=
  (forgottenProductIsLimit G).lift (Fan.mk _ (fun x =>
    (GodementRing.forgetSheaf X).map (Pi.π (GodementRing.pointTerm F) x) ≫ pointLift f x))

@[reassoc] theorem liftMap_component
    (f : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G) (x : X) :
    liftMap f ≫ (GodementRing.forgetSheaf X).map (Pi.π (GodementRing.pointTerm G) x) =
      (GodementRing.forgetSheaf X).map (Pi.π (GodementRing.pointTerm F) x) ≫ pointLift f x :=
  (forgottenProductIsLimit G).fac _ ⟨x⟩

theorem liftMap_id (F : GodementRing.RingSheaf X) :
    liftMap (𝟙 ((GodementRing.forgetSheaf X).obj F)) = 𝟙 _ := by
  apply godement_map_ext F
  intro x
  rw [liftMap_component]
  simp only [pointLift, stalkMap_id, skyscraperLift_id, Category.comp_id, Category.id_comp]

theorem liftMap_comp
    (f : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G)
    (g : (GodementRing.forgetSheaf X).obj G ⟶ (GodementRing.forgetSheaf X).obj H) :
    liftMap (f ≫ g) = liftMap f ≫ liftMap g := by
  apply godement_map_ext H
  intro x
  rw [liftMap_component, Category.assoc, liftMap_component, ← Category.assoc,
    liftMap_component, pointLift_comp, Category.assoc]

theorem liftMap_zero (F G : GodementRing.RingSheaf X) :
    liftMap (0 : (GodementRing.forgetSheaf X).obj F ⟶
      (GodementRing.forgetSheaf X).obj G) = 0 := by
  apply godement_map_ext G
  intro x
  rw [liftMap_component]
  simp only [pointLift, stalkMap_zero, skyscraperLift_zero,
    comp_zero, zero_comp]

theorem liftMap_add
    (f g : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G) :
    liftMap (f + g) = liftMap f + liftMap g := by
  apply godement_map_ext G
  intro x
  rw [liftMap_component, Preadditive.add_comp, liftMap_component, liftMap_component]
  simp only [pointLift, stalkMap_add, skyscraperLift_add, Preadditive.comp_add]

/-- Genuine ring morphisms prolong by exactly the original ring Godement functor. -/
theorem liftMap_ring (f : F ⟶ G) :
    liftMap ((GodementRing.forgetSheaf X).map f) =
      (GodementRing.forgetSheaf X).map (GodementRing.map f) := by
  apply godement_map_ext G
  intro x
  rw [liftMap_component, pointLift_ring]
  exact ((GodementRing.forgetSheaf X).map_comp _ _).symm.trans
    ((congrArg (GodementRing.forgetSheaf X).map (GodementRing.map_component f x)).trans
      ((GodementRing.forgetSheaf X).map_comp _ _)) |>.symm

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation
