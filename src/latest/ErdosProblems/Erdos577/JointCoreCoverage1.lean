import ErdosProblems.Erdos577.JointCoreCandidates

/-! Exhaustive bounded row coverage with diagonal mask 1. -/

namespace Erdos577.JointCore

private theorem coverage_0 : ∀ b c : Fin 16,
    7 ≤ rowSize 0 + rowSize c →
    13 ≤ rowSize 0 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 0 b c) || decide (Accepted 1 (pack 0 b c))) = true := by
  decide +kernel

private theorem coverage_1 : ∀ b c : Fin 16,
    7 ≤ rowSize 1 + rowSize c →
    13 ≤ rowSize 1 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 1 b c) || decide (Accepted 1 (pack 1 b c))) = true := by
  decide +kernel

private theorem coverage_2 : ∀ b c : Fin 16,
    7 ≤ rowSize 2 + rowSize c →
    13 ≤ rowSize 2 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 2 b c) || decide (Accepted 1 (pack 2 b c))) = true := by
  decide +kernel

private theorem coverage_3 : ∀ b c : Fin 16,
    7 ≤ rowSize 3 + rowSize c →
    13 ≤ rowSize 3 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 3 b c) || decide (Accepted 1 (pack 3 b c))) = true := by
  decide +kernel

private theorem coverage_4 : ∀ b c : Fin 16,
    7 ≤ rowSize 4 + rowSize c →
    13 ≤ rowSize 4 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 4 b c) || decide (Accepted 1 (pack 4 b c))) = true := by
  decide +kernel

private theorem coverage_5 : ∀ b c : Fin 16,
    7 ≤ rowSize 5 + rowSize c →
    13 ≤ rowSize 5 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 5 b c) || decide (Accepted 1 (pack 5 b c))) = true := by
  decide +kernel

private theorem coverage_6 : ∀ b c : Fin 16,
    7 ≤ rowSize 6 + rowSize c →
    13 ≤ rowSize 6 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 6 b c) || decide (Accepted 1 (pack 6 b c))) = true := by
  decide +kernel

private theorem coverage_7 : ∀ b c : Fin 16,
    7 ≤ rowSize 7 + rowSize c →
    13 ≤ rowSize 7 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 7 b c) || decide (Accepted 1 (pack 7 b c))) = true := by
  decide +kernel

private theorem coverage_8 : ∀ b c : Fin 16,
    7 ≤ rowSize 8 + rowSize c →
    13 ≤ rowSize 8 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 8 b c) || decide (Accepted 1 (pack 8 b c))) = true := by
  decide +kernel

private theorem coverage_9 : ∀ b c : Fin 16,
    7 ≤ rowSize 9 + rowSize c →
    13 ≤ rowSize 9 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 9 b c) || decide (Accepted 1 (pack 9 b c))) = true := by
  decide +kernel

private theorem coverage_10 : ∀ b c : Fin 16,
    7 ≤ rowSize 10 + rowSize c →
    13 ≤ rowSize 10 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 10 b c) || decide (Accepted 1 (pack 10 b c))) = true := by
  decide +kernel

private theorem coverage_11 : ∀ b c : Fin 16,
    7 ≤ rowSize 11 + rowSize c →
    13 ≤ rowSize 11 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 11 b c) || decide (Accepted 1 (pack 11 b c))) = true := by
  decide +kernel

private theorem coverage_12 : ∀ b c : Fin 16,
    7 ≤ rowSize 12 + rowSize c →
    13 ≤ rowSize 12 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 12 b c) || decide (Accepted 1 (pack 12 b c))) = true := by
  decide +kernel

private theorem coverage_13 : ∀ b c : Fin 16,
    7 ≤ rowSize 13 + rowSize c →
    13 ≤ rowSize 13 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 13 b c) || decide (Accepted 1 (pack 13 b c))) = true := by
  decide +kernel

private theorem coverage_14 : ∀ b c : Fin 16,
    7 ≤ rowSize 14 + rowSize c →
    13 ≤ rowSize 14 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 14 b c) || decide (Accepted 1 (pack 14 b c))) = true := by
  decide +kernel

private theorem coverage_15 : ∀ b c : Fin 16,
    7 ≤ rowSize 15 + rowSize c →
    13 ≤ rowSize 15 + rowSize b + 2 * rowSize c →
    (covered 1 (pack 15 b c) || decide (Accepted 1 (pack 15 b c))) = true := by
  decide +kernel

theorem row_coverage_1 (r b c : Fin 16)
    (houter : 7 ≤ rowSize r + rowSize c)
    (hweighted : 13 ≤ rowSize r + rowSize b + 2 * rowSize c) :
    (covered 1 (pack r b c) || decide (Accepted 1 (pack r b c))) = true := by
  fin_cases r
  · exact coverage_0 b c houter hweighted
  · exact coverage_1 b c houter hweighted
  · exact coverage_2 b c houter hweighted
  · exact coverage_3 b c houter hweighted
  · exact coverage_4 b c houter hweighted
  · exact coverage_5 b c houter hweighted
  · exact coverage_6 b c houter hweighted
  · exact coverage_7 b c houter hweighted
  · exact coverage_8 b c houter hweighted
  · exact coverage_9 b c houter hweighted
  · exact coverage_10 b c houter hweighted
  · exact coverage_11 b c houter hweighted
  · exact coverage_12 b c houter hweighted
  · exact coverage_13 b c houter hweighted
  · exact coverage_14 b c houter hweighted
  · exact coverage_15 b c houter hweighted

end Erdos577.JointCore
