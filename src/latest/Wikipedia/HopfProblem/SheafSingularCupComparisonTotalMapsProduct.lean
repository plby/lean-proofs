import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsValues

/-!
# The actual first and last component maps preserve the cochain cup product

The mixed component is calculated literally and is zero. The surviving
component preserves the Alexander--Whitney product because its original
ring map commutes with the original cofaces. No cocycle, exactness, or
cohomology comparison is assumed.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

open SheafCupProduct CuspNormalization

variable (X : TopCat.{0})

theorem first_cupOne
    (a b : (GodementRing.term1 (SheafConstants.complexSheaf X)).obj.obj (op ⊤)) :
    (TotalSheaf.globalData X).cupOne ((firstValues X).f1 a, 0) ((firstValues X).f1 b, 0) =
      ((firstValues X).f2 ((constantData X).cupOne a b), 0, 0) := by
  apply Prod.ext
  · exact ((firstValues X).cupOne_comm a b).symm
  · apply Prod.ext
    · simp [TotalAlgebra.Data.cupOne]
    · simp [TotalAlgebra.Data.cupOne]

theorem last_cupOne (a b : (RingCochains.sheaf X 1).obj.obj (op ⊤)) :
    (TotalSheaf.globalData X).cupOne (0, (lastValues X).f1 a) (0, (lastValues X).f1 b) =
      (0, 0, (lastValues X).f2 ((RingCochains.globalData X).cupOne a b)) := by
  apply Prod.ext
  · simp [TotalAlgebra.Data.cupOne]
  · apply Prod.ext
    · simp [TotalAlgebra.Data.cupOne]
    · exact ((lastValues X).cupOne_comm a b).symm

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps
