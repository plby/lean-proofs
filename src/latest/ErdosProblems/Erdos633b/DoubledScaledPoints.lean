import ErdosProblems.Erdos633b.DoubledCoordinates

/-! Cancellation-free coordinate expressions for the two radial cut points. -/

namespace Erdos633b.DoubledCoordinates

open Sixty

theorem pointE_eq (d a b m : ℝ) :
    pointE d a b m = point d (2 * m * a ^ 3 / (a + b))
      (2 * m * a ^ 2 * b / (a + b)) := by
  rw [pointE, pointD, ← point_smul]
  congr 1 <;> ring

theorem pointF_eq (d a b c m : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    pointF d a b c m = point d (2 * m * a * (a - b))
      (2 * m * a * b * (2 * a + b) / (a + b)) := by
  have hZ : 0 < a + b := add_pos ha hb
  have hP : 0 < a + 2 * b := by linarith
  rw [pointF, bigC, ← point_smul]
  congr 1 <;> dsimp only [cX, cY] <;> field_simp

end Erdos633b.DoubledCoordinates
