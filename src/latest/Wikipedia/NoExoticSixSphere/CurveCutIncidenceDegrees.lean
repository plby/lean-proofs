import Wikipedia.NoExoticSixSphere.FiniteCurveEdges
import Wikipedia.NoExoticSixSphere.CurveLocalIncidence
import Wikipedia.NoExoticSixSphere.CurveIntervalEndpointInterior
import Mathlib.Data.Set.Card

/-!
# Actual incidence degree one at the boundary and two elsewhere

The common zero-coordinate boundary identification excludes an interior cut
from the ambient interior of any component closure. This proves that its two
local branches represent distinct global edges. Boundary cuts have exactly
one incident edge. The degree is the cardinality of the actual incident
component set, not an assigned combinatorial value.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]

theorem cut_not_interior_component_closure (t : Finset ι) (N : ι → IntervalNeighborhood X)
    (hcov : univ ⊆ ⋃ i ∈ t, (N i).openSet) (B : Set X)
    (hB : ∀ i ∈ t, ∀ y ∈ (N i).chart.source,
      CurveChart.realCoordinate (N i).chart y = 0 ↔ y ∈ B)
    (v : X) (hv : v ∈ cutSet t N) (hvB : v ∉ B)
    (x : {x : X // x ∉ cutSet t N}) :
    v ∉ interior (closure (cutComponent (cutSet t N) x)) := by
  intro hvint
  obtain ⟨i, hi, m, hm⟩ := exists_cutComponent_marking t N hcov x
  have hBS := boundary_subset_cutSet t N hcov B hB
  have hz : ∀ y ∈ m.chart.source,
      CurveChart.realCoordinate m.chart y = 0 → y ∈ cutSet t N := by
    rw [hm]
    exact fun y hy hy0 ↦ hBS ((hB i hi y hy).mp hy0)
  have hne : CurveChart.realCoordinate m.chart v ≠ 0 := by
    intro he
    have hs := m.source (interior_subset hvint)
    rw [hm] at hs he
    exact hvB ((hB i hi v hs).mp he)
  have hpos : 0 < CurveChart.realCoordinate m.chart v :=
    lt_of_le_of_ne (m.chart v).property hne.symm
  have hcl := interior_subset hvint
  rw [m.closure_component_eq (finite_cutSet t N).isClosed x hz] at hcl
  rcases hcl with hmem | he | he
  · exact cutComponent_subset_compl (cutSet t N) x hmem hv
  · rw [he, m.left_coordinate] at hpos
    exact m.leftPoint_not_mem_interior_closure hpos (he ▸ hvint)
  · exact m.rightPoint_not_mem_interior_closure (he ▸ hvint)

theorem incidentComponents_ncard_at_cut (t : Finset ι) (N : ι → IntervalNeighborhood X)
    (hcov : univ ⊆ ⋃ i ∈ t, (N i).openSet) (B : Set X) [DecidablePred (· ∈ B)]
    (hB : ∀ i ∈ t, ∀ y ∈ (N i).chart.source,
      CurveChart.realCoordinate (N i).chart y = 0 ↔ y ∈ B)
    (v : X) (hv : v ∈ cutSet t N) :
    (incidentComponents (cutSet t N) v).ncard = if v ∈ B then 1 else 2 := by
  classical
  have hBS := boundary_subset_cutSet t N hcov B hB
  obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.mp (hcov (mem_univ v))
  obtain ⟨d, hde, hvd, hcut⟩ := exists_interval_avoiding_other_cuts (cutSet t N)
    (finite_cutSet t N) (N i).chart v hvi.1
  have hzero : ∀ y ∈ d.chart.source, (d.chart y).val = 0 → y ∈ cutSet t N := by
    intro y hy hy0
    rw [hde] at hy hy0
    exact hBS ((hB i hi y hy).mp hy0)
  by_cases hvB : v ∈ B
  · have hz : (d.chart v).val = 0 := by
      rw [hde]
      exact (hB i hi v hvi.1).mpr hvB
    obtain ⟨q, hq⟩ := d.incident_components_eq_singleton v hvd (cutSet t N) hv hcut hzero hz
    rw [hq, if_pos hvB]
    exact ncard_singleton _
  · have hpos : 0 < (d.chart v).val := by
      apply lt_of_le_of_ne (d.chart v).property
      intro he
      have hz : CurveChart.realCoordinate (N i).chart v = 0 := by
        rw [← hde]
        exact he.symm
      exact hvB ((hB i hi v hvi.1).mp hz)
    obtain ⟨p, q, hpq, he⟩ := d.incident_components_eq_pair v hvd (cutSet t N) hv hcut hzero
      hpos (cut_not_interior_component_closure t N hcov B hB v hv hvB)
    rw [he, if_neg hvB]
    exact ncard_pair hpq

end NoExoticSixSphere.CurveDecomposition
