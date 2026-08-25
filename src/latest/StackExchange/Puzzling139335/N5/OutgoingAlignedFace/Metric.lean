import StackExchange.Puzzling139335.SquareGeometry

/-! # Metric bounds for an actual interval on the square's top side -/

namespace Puzzling139335.N5.OutgoingAlignedFace

/-- Two points on the top side within the horizontal interval `[b,m]` have squared
distance at most the squared interval length. -/
theorem top_interval_dist_sq_le {X Y : Plane} {b m : ℝ}
    (hXtop : X 1 = 1) (hYtop : Y 1 = 1)
    (hXlo : b ≤ X 0) (hXhi : X 0 ≤ m) (hYlo : b ≤ Y 0) (hYhi : Y 0 ≤ m) :
    dist X Y ^ 2 ≤ (m - b) ^ 2 := by
  have hminus : 0 ≤ (m - b) - (X 0 - Y 0) := by linarith only [hXhi, hYlo]
  have hplus : 0 ≤ (m - b) + (X 0 - Y 0) := by linarith only [hYhi, hXlo]
  rw [plane_dist_sq, hXtop, hYtop]
  nlinarith only [mul_nonneg hminus hplus]

/-- Ending the interval strictly before one makes its squared length strictly smaller
than the squared length from the same starting point to one. -/
theorem interval_length_sq_lt {b m : ℝ} (hbm : b < m) (hm1 : m < 1) :
    (m - b) ^ 2 < (1 - b) ^ 2 := by
  have hsum : 0 < 1 + m - 2 * b := by linarith only [hbm, hm1]
  nlinarith only [mul_pos (sub_pos.mpr hm1) hsum]

end Puzzling139335.N5.OutgoingAlignedFace
