import Wikipedia.NoExoticSixSphere.CutCurveEndpointCuts

/-!
# The actual cut component is precisely the open marked interval

The coordinate image of the component is connected, approaches both marked
endpoints, and contains neither endpoint. The intermediate value theorem
therefore identifies it with the whole open interval. Its ambient closure
adds exactly the two actual marked points, and these are its entire frontier.
-/

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
  {S : Set X} (hS : IsClosed S) (x : {x : X // x ∉ S})
  (m : IntervalMarking (cutComponent S x))
  (hzero : ∀ y ∈ m.chart.source, CurveChart.realCoordinate m.chart y = 0 → y ∈ S)

include hS hzero

theorem IntervalMarking.image_component_eq_Ioo :
    CurveChart.realCoordinate m.chart '' cutComponent S x = Ioo m.left m.right := by
  have hc := (CurveChart.continuousOn_realCoordinate m.chart).mono m.source
  have hconn := (isConnected_cutComponent S x).image (CurveChart.realCoordinate m.chart)
    (hc.mono subset_closure)
  have hl : m.left ∈ closure (CurveChart.realCoordinate m.chart '' cutComponent S x) := by
    simpa only [m.left_coordinate] using
      hc.image_closure (mem_image_of_mem (CurveChart.realCoordinate m.chart) m.leftPoint.property)
  have hr : m.right ∈ closure (CurveChart.realCoordinate m.chart '' cutComponent S x) := by
    simpa only [m.right_coordinate] using
      hc.image_closure (mem_image_of_mem (CurveChart.realCoordinate m.chart) m.rightPoint.property)
  apply subset_antisymm
  · rintro r ⟨y, hy, rfl⟩
    have hb := m.point_bounds (subset_closure hy)
    constructor
    · apply lt_of_le_of_ne hb.1
      intro he
      have heq := m.eq_leftPoint_of_coordinate (subset_closure hy) he.symm
      exact m.leftPoint_not_mem_component hS x hzero (heq ▸ hy)
    · apply lt_of_le_of_ne hb.2
      intro he
      have heq := m.eq_rightPoint_of_coordinate (subset_closure hy) he
      exact m.rightPoint_not_mem_component hS x (heq ▸ hy)
  · intro r hrange
    obtain ⟨u, hu, huC⟩ := (mem_closure_iff.mp hl) (Iio r) isOpen_Iio hrange.1
    obtain ⟨v, hv, hvC⟩ := (mem_closure_iff.mp hr) (Ioi r) isOpen_Ioi hrange.2
    exact hconn.Icc_subset huC hvC ⟨hu.le, hv.le⟩

theorem IntervalMarking.mem_component_iff {y : X} (hy : y ∈ closure (cutComponent S x)) :
    y ∈ cutComponent S x ↔ CurveChart.realCoordinate m.chart y ∈ Ioo m.left m.right := by
  constructor
  · intro h
    rw [← m.image_component_eq_Ioo hS x hzero]
    exact mem_image_of_mem _ h
  · intro h
    rw [← m.image_component_eq_Ioo hS x hzero] at h
    obtain ⟨z, hz, he⟩ := h
    have heq := CurveChart.injOn_realCoordinate m.chart
      (m.source (subset_closure hz)) (m.source hy) he
    exact heq ▸ hz

theorem IntervalMarking.closure_component_eq :
    closure (cutComponent S x) = cutComponent S x ∪ {m.leftPoint.val, m.rightPoint.val} := by
  ext y
  constructor
  · intro hy
    have hb := m.point_bounds hy
    rcases lt_or_eq_of_le hb.1 with hl | hl
    · rcases lt_or_eq_of_le hb.2 with hr | hr
      · exact Or.inl ((m.mem_component_iff hS x hzero hy).mpr ⟨hl, hr⟩)
      · exact Or.inr (Or.inr (m.eq_rightPoint_of_coordinate hy hr))
    · exact Or.inr (Or.inl (m.eq_leftPoint_of_coordinate hy hl.symm))
  · rintro (hy | hy | hy)
    · exact subset_closure hy
    · exact hy.symm ▸ m.leftPoint.property
    · exact hy.symm ▸ m.rightPoint.property

theorem IntervalMarking.frontier_component_eq :
    frontier (cutComponent S x) = {m.leftPoint.val, m.rightPoint.val} := by
  rw [frontier, (isOpen_cutComponent hS x).interior_eq]
  ext y
  constructor
  · rintro ⟨hy, hn⟩
    rw [m.closure_component_eq hS x hzero] at hy
    exact hy.resolve_left hn
  · intro hy
    rcases hy with hy | hy
    · subst y
      exact ⟨m.leftPoint.property, m.leftPoint_not_mem_component hS x hzero⟩
    · have he := mem_singleton_iff.mp hy
      subst y
      exact ⟨m.rightPoint.property, m.rightPoint_not_mem_component hS x⟩

end NoExoticSixSphere.CurveDecomposition
