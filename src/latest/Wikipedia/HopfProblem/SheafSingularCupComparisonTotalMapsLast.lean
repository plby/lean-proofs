import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsCategorical

/-!
# The actual singular-cochain row maps into the total complex

The original Godement column unit kills its vertical differential.
Its original horizontal naturality squares identify the remaining
coordinates with the actual singular-cochain differentials.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

open SheafCupProduct

variable (X : TopCat.{0})

theorem last_comm0 :
    last0 X ≫ (TotalSheaf.categoryData X).d0 = RingCochains.d0 X ≫ last1 X :=
  last_square0 (TotalSheaf.categoryData X) _ _ _
    (GodementExact.augmentation_d0 (RingCochains.sheaf X 0)) (TotalSheaf.columnUnit_d0 X)

theorem last_comm1 :
    last1 X ≫ (TotalSheaf.categoryData X).d1 = RingCochains.d1 X ≫ last2 X :=
  last_square1 (TotalSheaf.categoryData X) _ _ _
    (GodementExact.augmentation_d0 (RingCochains.sheaf X 1)) (TotalSheaf.columnUnit_d1 X)

theorem last_comm2 :
    last2 X ≫ (TotalSheaf.categoryData X).d2 = RingCochains.d2 X ≫ last3 X :=
  last_square2 (TotalSheaf.categoryData X) _ _ _
    (GodementExact.augmentation_d0 (RingCochains.sheaf X 2)) (TotalSheaf.columnUnit_d2 X)

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps
