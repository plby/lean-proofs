import ErdosProblems.Erdos633b.DoubledDimensions

/-! The exact five-region count equals the area-predicted integer polynomial. -/

namespace Erdos633b.DoubledDimensions

open Sixty DoubledPartition

def pieceCount (a b c : ℕ) : Piece → ℕ
  | .abd => (outerScale a b c * c) ^ 2
  | .bdg => (outerScale a b c * c) ^ 2
  | .aef => smallScale a b c ^ 2
  | .cfg => cornerScale a b c ^ 2 * (commonScale a b ^ 2 * b * (a + b))
  | .trapezoid => trapezoidCount a b c

theorem five_count_identity (a b c : ℕ) (hab : a ≤ b)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (∑ k, pieceCount a b c k) = outerScale a b c ^ 2 * (a + 2 * b) * (2 * a + b) := by
  have hu : (Finset.univ : Finset Piece) = {.abd, .bdg, .aef, .cfg, .trapezoid} := rfl
  rw [hu]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, or_self, not_false_eq_true, pieceCount]
  apply Nat.cast_injective (R := ℝ)
  push_cast
  dsimp only [outerScale, smallScale, cornerScale, trapezoidCount, widthUnits, heightUnits]
  push_cast [Nat.cast_sub hab]
  have hrelr : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + (a : ℝ) * b + (b : ℝ) ^ 2 := by exact_mod_cast hrel
  linear_combination (commonScale a b : ℝ) ^ 2 * (c : ℝ) ^ 4 *
    (2 * (b : ℝ) ^ 2 * ((a : ℝ) + b) ^ 2 + 4 * (a : ℝ) ^ 2 * (b : ℝ) ^ 2 +
      (a : ℝ) * b * ((b : ℝ) - a) * ((a : ℝ) + 3 * b)) * hrelr

end Erdos633b.DoubledDimensions
