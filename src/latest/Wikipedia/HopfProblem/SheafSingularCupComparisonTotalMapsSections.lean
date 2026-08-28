import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsProduct
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsFunctor
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalSheafGlobal

/-!
# The original global total maps have the literal first and last coordinates

The comparisons are the canonical images of actual biproduct
projections. Thus the product calculations apply to the original maps
on global sections, not to independently chosen cochain functions.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

open SheafCupProduct CuspNormalization
open SheafCohomologyResolution

variable (X : TopCat.{0})

theorem first1_global
    (a : (GodementRing.term1 (SheafConstants.complexSheaf X)).obj.obj (op ⊤)) :
    TotalSheaf.globalOneEquiv X ((globalSectionsFunctor X).map (first1 X) a) =
      ((firstValues X).f1 a, 0) :=
  oneEquiv_first (TotalSheaf.categoryData X) (globalSectionsFunctor X)
    (GodementExact.I1Map (RingCochains.augmentation X)) a

theorem first2_global
    (a : (GodementRing.term2 (SheafConstants.complexSheaf X)).obj.obj (op ⊤)) :
    TotalSheaf.globalTwoEquiv X ((globalSectionsFunctor X).map (first2 X) a) =
      ((firstValues X).f2 a, 0, 0) :=
  twoEquiv_first (TotalSheaf.categoryData X) (globalSectionsFunctor X)
    (GodementExact.I2Map (RingCochains.augmentation X)) a

theorem last1_global (a : (RingCochains.sheaf X 1).obj.obj (op ⊤)) :
    TotalSheaf.globalOneEquiv X ((globalSectionsFunctor X).map (last1 X) a) =
      (0, (lastValues X).f1 a) :=
  oneEquiv_last (TotalSheaf.categoryData X) (globalSectionsFunctor X)
    (TotalSheaf.columnUnit X 1) a

theorem last2_global (a : (RingCochains.sheaf X 2).obj.obj (op ⊤)) :
    TotalSheaf.globalTwoEquiv X ((globalSectionsFunctor X).map (last2 X) a) =
      (0, 0, (lastValues X).f2 a) :=
  twoEquiv_last (TotalSheaf.categoryData X) (globalSectionsFunctor X)
    (TotalSheaf.columnUnit X 2) a

/-- The original first-column global-section map preserves the actual cochain cup product. -/
theorem first_global_cup
    (a b : (GodementRing.term1 (SheafConstants.complexSheaf X)).obj.obj (op ⊤)) :
    (TotalSheaf.globalData X).cupOne
        (TotalSheaf.globalOneEquiv X ((globalSectionsFunctor X).map (first1 X) a))
        (TotalSheaf.globalOneEquiv X ((globalSectionsFunctor X).map (first1 X) b)) =
      TotalSheaf.globalTwoEquiv X
        ((globalSectionsFunctor X).map (first2 X) ((constantData X).cupOne a b)) :=
  (congrArg₂ (TotalSheaf.globalData X).cupOne (first1_global X a) (first1_global X b)).trans
    ((first_cupOne X a b).trans (first2_global X ((constantData X).cupOne a b)).symm)

/-- The original last-row global-section map preserves the actual cochain cup product. -/
theorem last_global_cup (a b : (RingCochains.sheaf X 1).obj.obj (op ⊤)) :
    (TotalSheaf.globalData X).cupOne
        (TotalSheaf.globalOneEquiv X ((globalSectionsFunctor X).map (last1 X) a))
        (TotalSheaf.globalOneEquiv X ((globalSectionsFunctor X).map (last1 X) b)) =
      TotalSheaf.globalTwoEquiv X
        ((globalSectionsFunctor X).map (last2 X) ((RingCochains.globalData X).cupOne a b)) :=
  (congrArg₂ (TotalSheaf.globalData X).cupOne (last1_global X a) (last1_global X b)).trans
    ((last_cupOne X a b).trans (last2_global X ((RingCochains.globalData X).cupOne a b)).symm)

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps
