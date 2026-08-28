import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsCategorical

/-!
# The genuine Godement map into the first column is a cochain map

The vertical squares are the original Godement naturality squares.
The other total coordinates vanish because actual constant singular
cochains have equal endpoint restrictions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

open SheafCupProduct CuspNormalization

variable (X : TopCat.{0})

theorem first_comm0 :
    first0 X ≫ (TotalSheaf.categoryData X).d0 =
      GodementExact.d0 (SheafConstants.complexSheaf X) ≫ first1 X :=
  first_square0 (TotalSheaf.categoryData X) _ _ _
    (GodementExact.d0_naturality (RingCochains.augmentation X)) (first0_horizontal X)

theorem first_comm1 :
    first1 X ≫ (TotalSheaf.categoryData X).d1 =
      GodementExact.d1 (SheafConstants.complexSheaf X) ≫ first2 X :=
  first_square1 (TotalSheaf.categoryData X) _ _ _
    (GodementExact.d1_naturality (RingCochains.augmentation X)) (first1_horizontal X)

theorem first_comm2 :
    first2 X ≫ (TotalSheaf.categoryData X).d2 =
      GodementExact.d2 (SheafConstants.complexSheaf X) ≫ first3 X :=
  first_square2 (TotalSheaf.categoryData X) _ _ _
    (GodementExact.d2_naturality (RingCochains.augmentation X)) (first2_horizontal X)

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps
