import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalSheafColumnsBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryComplex
import Wikipedia.HopfProblem.SheafSingularCupComparisonRingAugmentation

/-!
# The actual augmented total terms

The augmentation first includes the original constant sheaf into the
actual singular-cochain sheaf and then takes its genuine germ map.
The total differentials are the original signed categorical maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf

open SheafCupProduct CuspNormalization

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

private theorem compose_square_zero {C : Type*} [Category* C] [HasZeroMorphisms C]
    {A B E G H : C} (a : A ⟶ B) (i : B ⟶ E) (d : E ⟶ H)
    (b : B ⟶ G) (j : G ⟶ H) (hs : i ≫ d = b ≫ j) (hz : a ≫ b = 0) :
    (a ≫ i) ≫ d = 0 := by
  rw [Category.assoc, hs, ← Category.assoc, hz, zero_comp]

variable (X : TopCat.{0})

abbrev I0 := (categoryData X).zeroTerm
abbrev I1 := (categoryData X).oneTerm
abbrev I2 := (categoryData X).twoTerm
abbrev I3 := (categoryData X).threeTerm

abbrev d0 := (categoryData X).d0
abbrev d1 := (categoryData X).d1
abbrev d2 := (categoryData X).d2

/-- The original constant-sheaf inclusion followed by the original germ inclusion. -/
def augmentation : SheafConstants.complexAdditiveSheaf X ⟶ I0 X :=
  (GodementRing.forgetSheaf X).map (RingCochains.augmentation X) ≫ columnUnit X 0

private theorem row_augmentation_d0 :
    (GodementRing.forgetSheaf X).map (RingCochains.augmentation X) ≫
      RingCochains.d0 X = 0 := by
  change (GodementRing.forgetSheaf X).map (RingCochains.augmentation X) ≫
    ((GodementRing.forgetSheaf X).map (RingCochains.coface X 0 0) -
      (GodementRing.forgetSheaf X).map (RingCochains.coface X 0 1)) = 0
  rw [Preadditive.comp_sub]
  apply sub_eq_zero.mpr
  exact ((GodementRing.forgetSheaf X).map_comp (RingCochains.augmentation X)
      (RingCochains.coface X 0 0)).symm.trans
    ((congrArg (GodementRing.forgetSheaf X).map (RingCochains.augmentation_coface X)).trans
      ((GodementRing.forgetSheaf X).map_comp (RingCochains.augmentation X)
        (RingCochains.coface X 0 1)))

theorem augmentation_d0 : augmentation X ≫ d0 X = 0 := by
  apply biprod.hom_ext
  · change augmentation X ≫ (categoryData X).d0 ≫ biprod.fst = 0 ≫ biprod.fst
    rw [TotalCategory.Data.d0_fst, zero_comp]
    change ((GodementRing.forgetSheaf X).map (RingCochains.augmentation X) ≫
      columnUnit X 0) ≫ GodementExact.d0 (RingCochains.sheaf X 0) = 0
    rw [Category.assoc, GodementExact.augmentation_d0, comp_zero]
  · change augmentation X ≫ (categoryData X).d0 ≫ biprod.snd = 0 ≫ biprod.snd
    rw [TotalCategory.Data.d0_snd, zero_comp]
    change ((GodementRing.forgetSheaf X).map (RingCochains.augmentation X) ≫
      columnUnit X 0) ≫ (categoryData X).h00 = 0
    exact compose_square_zero
      ((GodementRing.forgetSheaf X).map (RingCochains.augmentation X))
      (columnUnit X 0) (categoryData X).h00 (RingCochains.d0 X) (columnUnit X 1)
      (columnUnit_d0 X) (row_augmentation_d0 X)

abbrev initialComplex := ShortComplex.mk (augmentation X) (d0 X) (augmentation_d0 X)
abbrev oneComplex := (categoryData X).oneComplex
abbrev twoComplex := (categoryData X).twoComplex

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf
