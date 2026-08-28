import Wikipedia.NoExoticSixSphere.CutCurveIntervalMarking
import Wikipedia.NoExoticSixSphere.HalfLineOpenExtrema

/-!
# Both actual interval endpoints belong to the cut set

An endpoint outside the cuts would lie in the open component. In the original
half-line chart this would give a maximum or a positive minimum of an open
region. A zero minimum is excluded by the actual boundary-to-cut inclusion.
The exact coordinate identity of the interval marking supplies the bounds.
-/

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

open HalfLineIntervals

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
  {S : Set X} (hS : IsClosed S) (x : {x : X // x ∉ S})
  (m : IntervalMarking (cutComponent S x))

include hS

theorem IntervalMarking.leftPoint_mem_cuts
    (hzero : ∀ y ∈ m.chart.source, CurveChart.realCoordinate m.chart y = 0 → y ∈ S) :
    m.leftPoint.val ∈ S := by
  by_contra hn
  have hp := closure_cutComponent_away_from_cuts x m.leftPoint.property hn
  have hc : cutComponent S x ⊆ m.chart.source := subset_closure.trans m.source
  have hopen := (m.chart.isOpen_image_iff_of_subset_source hc).mpr (isOpen_cutComponent hS x)
  have hpos : 0 < (m.chart m.leftPoint.val).val := by
    apply lt_of_le_of_ne (m.chart m.leftPoint.val).property
    intro he
    exact hn (hzero _ (m.source m.leftPoint.property) he.symm)
  obtain ⟨z, ⟨y, hy, hyz⟩, hzy⟩ := exists_lt_in_open hopen (m.chart m.leftPoint.val)
    (mem_image_of_mem m.chart hp) hpos
  have hlo := (m.point_bounds (subset_closure hy)).1
  have hlt : CurveChart.realCoordinate m.chart y < m.left := by
    rw [← m.left_coordinate]
    change (m.chart y).val < (m.chart m.leftPoint.val).val
    rw [hyz]
    exact hzy
  exact (not_lt_of_ge hlo) hlt

theorem IntervalMarking.rightPoint_mem_cuts : m.rightPoint.val ∈ S := by
  by_contra hn
  have hp := closure_cutComponent_away_from_cuts x m.rightPoint.property hn
  have hc : cutComponent S x ⊆ m.chart.source := subset_closure.trans m.source
  have hopen := (m.chart.isOpen_image_iff_of_subset_source hc).mpr (isOpen_cutComponent hS x)
  obtain ⟨z, ⟨y, hy, hyz⟩, hzy⟩ := exists_gt_in_open hopen (m.chart m.rightPoint.val)
    (mem_image_of_mem m.chart hp)
  have hup := (m.point_bounds (subset_closure hy)).2
  have hlt : m.right < CurveChart.realCoordinate m.chart y := by
    rw [← m.right_coordinate]
    change (m.chart m.rightPoint.val).val < (m.chart y).val
    rw [hyz]
    exact hzy
  exact (not_lt_of_ge hup) hlt

theorem IntervalMarking.leftPoint_not_mem_component
    (hzero : ∀ y ∈ m.chart.source, CurveChart.realCoordinate m.chart y = 0 → y ∈ S) :
    m.leftPoint.val ∉ cutComponent S x := by
  intro hp
  exact cutComponent_subset_compl S x hp (m.leftPoint_mem_cuts hS x hzero)

theorem IntervalMarking.rightPoint_not_mem_component :
    m.rightPoint.val ∉ cutComponent S x := by
  intro hp
  exact cutComponent_subset_compl S x hp (m.rightPoint_mem_cuts hS x)

end NoExoticSixSphere.CurveDecomposition
