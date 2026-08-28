import ErdosProblems.Erdos577.TripleCoreCandidates

/-! Bounded kernel proofs that every complete or allowed diamond ten-contact core has a pattern. -/

namespace Erdos577.TripleCorePatterns

open JointCore

private theorem coverage_0 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 0 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 0 b c)) → Accepted d (pack 0 b c) := by
  decide +kernel

private theorem coverage_1 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 1 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 1 b c)) → Accepted d (pack 1 b c) := by
  decide +kernel

private theorem coverage_2 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 2 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 2 b c)) → Accepted d (pack 2 b c) := by
  decide +kernel

private theorem coverage_3 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 3 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 3 b c)) → Accepted d (pack 3 b c) := by
  decide +kernel

private theorem coverage_4 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 4 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 4 b c)) → Accepted d (pack 4 b c) := by
  decide +kernel

private theorem coverage_5 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 5 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 5 b c)) → Accepted d (pack 5 b c) := by
  decide +kernel

private theorem coverage_6 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 6 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 6 b c)) → Accepted d (pack 6 b c) := by
  decide +kernel

private theorem coverage_7 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 7 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 7 b c)) → Accepted d (pack 7 b c) := by
  decide +kernel

private theorem coverage_8 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 8 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 8 b c)) → Accepted d (pack 8 b c) := by
  decide +kernel

private theorem coverage_9 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 9 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 9 b c)) → Accepted d (pack 9 b c) := by
  decide +kernel

private theorem coverage_10 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 10 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 10 b c)) → Accepted d (pack 10 b c) := by
  decide +kernel

private theorem coverage_11 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 11 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 11 b c)) → Accepted d (pack 11 b c) := by
  decide +kernel

private theorem coverage_12 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 12 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 12 b c)) → Accepted d (pack 12 b c) := by
  decide +kernel

private theorem coverage_13 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 13 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 13 b c)) → Accepted d (pack 13 b c) := by
  decide +kernel

private theorem coverage_14 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 14 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 14 b c)) → Accepted d (pack 14 b c) := by
  decide +kernel

private theorem coverage_15 : ∀ d : Fin 4, ∀ b c : Fin 16,
    rowSize 15 + rowSize b + rowSize c = 10 →
    (d = 3 ∨ DenseTriangle.DiamondRows d (pack 15 b c)) → Accepted d (pack 15 b c) := by
  decide +kernel

theorem rows_classified (d : Fin 4) (r b c : Fin 16)
    (hcount : rowSize r + rowSize b + rowSize c = 10)
    (hshape : d = 3 ∨ DenseTriangle.DiamondRows d (pack r b c)) :
    Classified d (pack r b c) := by
  apply accepted_classified
  fin_cases r
  · exact coverage_0 d b c hcount hshape
  · exact coverage_1 d b c hcount hshape
  · exact coverage_2 d b c hcount hshape
  · exact coverage_3 d b c hcount hshape
  · exact coverage_4 d b c hcount hshape
  · exact coverage_5 d b c hcount hshape
  · exact coverage_6 d b c hcount hshape
  · exact coverage_7 d b c hcount hshape
  · exact coverage_8 d b c hcount hshape
  · exact coverage_9 d b c hcount hshape
  · exact coverage_10 d b c hcount hshape
  · exact coverage_11 d b c hcount hshape
  · exact coverage_12 d b c hcount hshape
  · exact coverage_13 d b c hcount hshape
  · exact coverage_14 d b c hcount hshape
  · exact coverage_15 d b c hcount hshape

end Erdos577.TripleCorePatterns
