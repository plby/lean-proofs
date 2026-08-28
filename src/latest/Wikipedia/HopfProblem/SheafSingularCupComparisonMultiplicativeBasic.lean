import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalNativeMaps
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMaps
import Wikipedia.HopfProblem.SheafSingularCupComparisonRowGlobal
import Wikipedia.HopfProblem.SheafCupProductFunctions

/-!
# The two actual product diagrams in the total resolution

The first-column and last-row cochain products have already been checked
literally, including their mixed components. Here their original quotient
maps are composed with the proved native Ext comparisons. No comparison
map or cup product is redefined to make these identities hold.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison

open CuspNormalization SheafCupProduct ConstantSheafSingularComparison

variable (X : TopCat.{0}) (hLC : LocallyContractibleSpace X)

/-- The actual total comparison preserves the original native Godement cup. -/
theorem native_total_cup
    (a b : CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1) :
    TotalSheaf.nativeTwoEquiv X hLC (constantCup X a b) =
      (TotalSheaf.globalData X).cup
        (TotalSheaf.nativeOneEquiv X hLC a) (TotalSheaf.nativeOneEquiv X hLC b) := by
  calc
    TotalSheaf.nativeTwoEquiv X hLC (constantCup X a b) =
        TotalMaps.firstH2 X
          (h2CofaceEquiv (SheafConstants.complexSheaf X) (constantScalarEnd X)
            (constantCup X a b)) :=
      (TotalNativeMaps.first_h2_native_apply X hLC _).symm
    _ = TotalMaps.firstH2 X
        ((globalData (SheafConstants.complexSheaf X)).cup
          (h1CofaceEquiv (SheafConstants.complexSheaf X) (constantScalarEnd X) a)
          (h1CofaceEquiv (SheafConstants.complexSheaf X) (constantScalarEnd X) b)) :=
      congrArg (TotalMaps.firstH2 X)
        (cup_comparison (SheafConstants.complexSheaf X) (constantScalarEnd X) a b)
    _ = (TotalSheaf.globalData X).cup
        (TotalMaps.firstH1 X
          (h1CofaceEquiv (SheafConstants.complexSheaf X) (constantScalarEnd X) a))
        (TotalMaps.firstH1 X
          (h1CofaceEquiv (SheafConstants.complexSheaf X) (constantScalarEnd X) b)) :=
      TotalMaps.firstH_cup X _ _
    _ = (TotalSheaf.globalData X).cup
        (TotalSheaf.nativeOneEquiv X hLC a) (TotalSheaf.nativeOneEquiv X hLC b) :=
      congrArg₂ (fun c d => (TotalSheaf.globalData X).cup c d)
        (TotalNativeMaps.first_h1_native_apply X hLC a)
        (TotalNativeMaps.first_h1_native_apply X hLC b)

/-- The actual singular unit followed by the last row preserves the literal AW cup. -/
theorem singular_total_cup
    (a b : (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 1) :
    TotalMaps.lastH2 X (RowGlobal.unitTwo X (Singular.cupProduct X a b)) =
      (TotalSheaf.globalData X).cup
        (TotalMaps.lastH1 X (RowGlobal.unitOne X a))
        (TotalMaps.lastH1 X (RowGlobal.unitOne X b)) :=
  (congrArg (TotalMaps.lastH2 X) (RowGlobal.unit_cup X a b)).trans
    (TotalMaps.lastH_cup X _ _)

variable [CompactSpace X] [T2Space X]

/-- The original sheaf/singular degree-one comparison gives the actual total map. -/
theorem comparison_total_one
    (a : CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1) :
    TotalMaps.lastH1 X (RowGlobal.unitOne X (complexSheafH1Equiv X hLC a)) =
      TotalSheaf.nativeOneEquiv X hLC a :=
  (congrArg (TotalMaps.lastH1 X) (RowGlobal.complexSheafH1Equiv_unit X hLC a)).trans
    (TotalNativeMaps.last_h1_native_apply X hLC a)

/-- The original degree-two comparison likewise gives the actual total map. -/
theorem comparison_total_two
    (a : CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 2) :
    TotalMaps.lastH2 X (RowGlobal.unitTwo X (complexSheafH2Equiv X hLC a)) =
      TotalSheaf.nativeTwoEquiv X hLC a :=
  (congrArg (TotalMaps.lastH2 X) (RowGlobal.complexSheafH2Equiv_unit X hLC a)).trans
    (TotalNativeMaps.last_h2_native_apply X hLC a)

end Wikipedia.HopfProblem.SheafSingularCupComparison
