import Wikipedia.NoExoticSixSphere.CutCurveIntervalMarking
import Wikipedia.NoExoticSixSphere.HalfLineOpenExtrema

/-!
# Marked endpoints cannot be ambient interior points of their interval closure

The upper endpoint is never an ambient interior point. The lower endpoint
can only be one at chart-coordinate zero. This uses the actual coordinate
map and will prevent two local branches at an interior cut from belonging
to the same global component.
-/

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

open HalfLineIntervals

variable {X : Type*} [TopologicalSpace X] {C : Set X}

theorem IntervalMarking.leftPoint_not_mem_interior_closure (m : IntervalMarking C)
    (hpos : 0 < m.left) : m.leftPoint.val ∉ interior (closure C) := by
  intro hp
  have hs : interior (closure C) ⊆ m.chart.source := interior_subset.trans m.source
  have hopen := (m.chart.isOpen_image_iff_of_subset_source hs).mpr isOpen_interior
  have hv : 0 < (m.chart m.leftPoint.val).val := by
    change 0 < CurveChart.realCoordinate m.chart m.leftPoint.val
    rw [m.left_coordinate]
    exact hpos
  obtain ⟨z, ⟨y, hy, hyz⟩, hzy⟩ := exists_lt_in_open hopen (m.chart m.leftPoint.val)
    (mem_image_of_mem m.chart hp) hv
  have hlo := (m.point_bounds (interior_subset hy)).1
  have hlt : CurveChart.realCoordinate m.chart y < m.left := by
    rw [← m.left_coordinate]
    change (m.chart y).val < (m.chart m.leftPoint.val).val
    rw [hyz]
    exact hzy
  exact (not_lt_of_ge hlo) hlt

theorem IntervalMarking.rightPoint_not_mem_interior_closure (m : IntervalMarking C) :
    m.rightPoint.val ∉ interior (closure C) := by
  intro hp
  have hs : interior (closure C) ⊆ m.chart.source := interior_subset.trans m.source
  have hopen := (m.chart.isOpen_image_iff_of_subset_source hs).mpr isOpen_interior
  obtain ⟨z, ⟨y, hy, hyz⟩, hzy⟩ := exists_gt_in_open hopen (m.chart m.rightPoint.val)
    (mem_image_of_mem m.chart hp)
  have hup := (m.point_bounds (interior_subset hy)).2
  have hlt : m.right < CurveChart.realCoordinate m.chart y := by
    rw [← m.right_coordinate]
    change (m.chart m.rightPoint.val).val < (m.chart y).val
    rw [hyz]
    exact hzy
  exact (not_lt_of_ge hup) hlt

end NoExoticSixSphere.CurveDecomposition
