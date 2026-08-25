import StackExchange.Puzzling139335.Definitions

/-! Local interior sides at an actual straight boundary segment. -/

open Set

namespace Puzzling139335.SegmentCrossing

/-- Near `x`, the strict side of the linear functional `f` is inside `P`. -/
def HasInteriorHalfBall (P : Set Plane) (x : Plane) (f : Plane →L[ℝ] ℝ) : Prop :=
  ∃ r > 0, Metric.ball x r ∩ {y | f x < f y} ⊆ interior P

end Puzzling139335.SegmentCrossing
