import ErdosProblems.Erdos577.JointCoreCoverage0
import ErdosProblems.Erdos577.JointCoreCoverage1
import ErdosProblems.Erdos577.JointCoreCoverage2
import ErdosProblems.Erdos577.JointCoreCoverage3

/-! A pattern or an actual strict improvement for every admissible triple of rows. -/

namespace Erdos577.JointCore

theorem row_coverage (d : Fin 4) (r b c : Fin 16)
    (houter : 7 ≤ rowSize r + rowSize c)
    (hweighted : 13 ≤ rowSize r + rowSize b + 2 * rowSize c) :
    (covered d (pack r b c) || decide (Accepted d (pack r b c))) = true := by
  fin_cases d
  · exact row_coverage_0 r b c houter hweighted
  · exact row_coverage_1 r b c houter hweighted
  · exact row_coverage_2 r b c houter hweighted
  · exact row_coverage_3 r b c houter hweighted

theorem rows_classified (d : Fin 4) (r b c : Fin 16)
    (houter : 7 ≤ rowSize r + rowSize c)
    (hweighted : 13 ≤ rowSize r + rowSize b + 2 * rowSize c) :
    DenseTriangle.Positive d (pack r b c) ∨ Classified d (pack r b c) := by
  rcases Bool.or_eq_true_iff.mp (row_coverage d r b c houter hweighted) with h | h
  · exact Or.inl (covered_positive d _ h)
  · exact Or.inr (accepted_classified d _ (of_decide_eq_true h))

end Erdos577.JointCore
