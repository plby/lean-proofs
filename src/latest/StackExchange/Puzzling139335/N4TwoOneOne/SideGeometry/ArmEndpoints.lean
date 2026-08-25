import StackExchange.Puzzling139335.N4TwoOneOne.SideGeometry.Reflection

/-! Recovering the actual incoming source-arm endpoint from a side contact. -/

open Set

namespace Puzzling139335.N4TwoOneOne

theorem rightMap_incomingEnd (θ u v R : ℝ) :
    rightMap θ u v (incomingEnd θ u v R) = (!₂[1, 1 - R] : Plane) := by
  ext i
  fin_cases i <;> dsimp [rightMap, incomingEnd, sourceCorner, eCoord, fCoord]
  · linear_combination u * (Real.sin_sq_add_cos_sq θ)
  · linear_combination (v - R) * (Real.sin_sq_add_cos_sq θ)

namespace SourceData

variable {d : SquareDissection} {θ u v : ℝ}

theorem incomingEnd_mem_of_right_side_contact (h : SourceData d θ u v) {l : ℝ}
    (hl : (!₂[1, l] : Plane) ∈ d.piece 1) :
    incomingEnd θ u v (1 - l) ∈ d.piece 0 := by
  apply h.mem_source_of_rightMap_mem
  simpa only [rightMap_incomingEnd, sub_sub_cancel] using hl

end SourceData

end Puzzling139335.N4TwoOneOne
