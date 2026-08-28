import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalSheafBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonRingDifferential
import Wikipedia.HopfProblem.SheafCupProductGodementExactMaps
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryMap

/-!
# The original augmented columns of the Godement--singular diagram

The four column augmentations are literal section-to-germs maps.
Their horizontal squares follow from the original naturality of that
map on each actual singular coface.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf

open SheafCupProduct

variable (X : TopCat.{0})

/-- The original augmentation of the `n`th Godement column. -/
abbrev columnUnit (n : ℕ) := GodementExact.augmentation (RingCochains.sheaf X n)

theorem columnUnit_d0 :
    columnUnit X 0 ≫ (categoryData X).h00 = RingCochains.d0 X ≫ columnUnit X 1 := by
  change GodementExact.augmentation (RingCochains.sheaf X 0) ≫
      (GodementExact.I0Map (RingCochains.coface X 0 0) -
        GodementExact.I0Map (RingCochains.coface X 0 1)) =
    ((GodementRing.forgetSheaf X).map (RingCochains.coface X 0 0) -
      (GodementRing.forgetSheaf X).map (RingCochains.coface X 0 1)) ≫
        GodementExact.augmentation (RingCochains.sheaf X 1)
  rw [Preadditive.comp_sub, Preadditive.sub_comp,
    ← GodementExact.augmentation_naturality, ← GodementExact.augmentation_naturality]

theorem columnUnit_d1 :
    columnUnit X 1 ≫ (categoryData X).h01 = RingCochains.d1 X ≫ columnUnit X 2 := by
  change GodementExact.augmentation (RingCochains.sheaf X 1) ≫
      (GodementExact.I0Map (RingCochains.coface X 1 0) -
        GodementExact.I0Map (RingCochains.coface X 1 1) +
        GodementExact.I0Map (RingCochains.coface X 1 2)) =
    ((GodementRing.forgetSheaf X).map (RingCochains.coface X 1 0) -
      (GodementRing.forgetSheaf X).map (RingCochains.coface X 1 1) +
      (GodementRing.forgetSheaf X).map (RingCochains.coface X 1 2)) ≫
        GodementExact.augmentation (RingCochains.sheaf X 2)
  simp only [Preadditive.comp_add, Preadditive.comp_sub,
    Preadditive.add_comp, Preadditive.sub_comp, ← GodementExact.augmentation_naturality]

theorem columnUnit_d2 :
    columnUnit X 2 ≫ (categoryData X).h02 = RingCochains.d2 X ≫ columnUnit X 3 := by
  change GodementExact.augmentation (RingCochains.sheaf X 2) ≫
      (GodementExact.I0Map (RingCochains.coface X 2 0) -
        GodementExact.I0Map (RingCochains.coface X 2 1) +
        GodementExact.I0Map (RingCochains.coface X 2 2) -
        GodementExact.I0Map (RingCochains.coface X 2 3)) =
    ((GodementRing.forgetSheaf X).map (RingCochains.coface X 2 0) -
      (GodementRing.forgetSheaf X).map (RingCochains.coface X 2 1) +
      (GodementRing.forgetSheaf X).map (RingCochains.coface X 2 2) -
      (GodementRing.forgetSheaf X).map (RingCochains.coface X 2 3)) ≫
        GodementExact.augmentation (RingCochains.sheaf X 3)
  simp only [Preadditive.comp_add, Preadditive.comp_sub,
    Preadditive.add_comp, Preadditive.sub_comp, ← GodementExact.augmentation_naturality]

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf
