import Wikipedia.NoExoticSixSphere.CurveCutIncidenceDegrees

/-!
# Each actual component edge has exactly two incident cuts

The intersection of a component closure with the cut set is precisely the two
marked endpoints. Both endpoints are actual cuts, and all component points
avoid the cuts. The nondegenerate marking proves the two endpoints distinct.
-/

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]

theorem edge_cut_intersection_ncard (t : Finset ι) (N : ι → IntervalNeighborhood X)
    (hcov : univ ⊆ ⋃ i ∈ t, (N i).openSet)
    (hzero : ∀ i ∈ t, ∀ y ∈ (N i).chart.source,
      CurveChart.realCoordinate (N i).chart y = 0 → y ∈ cutSet t N)
    (C : Set X) (hC : C ∈ componentSet (cutSet t N)) :
    (cutSet t N ∩ closure C).ncard = 2 := by
  obtain ⟨x, rfl⟩ := hC
  obtain ⟨i, hi, m, hm⟩ := exists_cutComponent_marking t N hcov x
  have hz : ∀ y ∈ m.chart.source,
      CurveChart.realCoordinate m.chart y = 0 → y ∈ cutSet t N := by
    rw [hm]
    exact hzero i hi
  have hl := m.leftPoint_mem_cuts (finite_cutSet t N).isClosed x hz
  have hr := m.rightPoint_mem_cuts (finite_cutSet t N).isClosed x
  have he : cutSet t N ∩ closure (cutComponent (cutSet t N) x) =
      {m.leftPoint.val, m.rightPoint.val} := by
    ext v
    constructor
    · rintro ⟨hvS, hvC⟩
      rw [m.closure_component_eq (finite_cutSet t N).isClosed x hz] at hvC
      exact hvC.resolve_left (fun h ↦ cutComponent_subset_compl (cutSet t N) x h hvS)
    · rintro (hv | hv)
      · subst v
        exact ⟨hl, m.leftPoint.property⟩
      · have he := mem_singleton_iff.mp hv
        subst v
        exact ⟨hr, m.rightPoint.property⟩
  rw [he]
  exact ncard_pair m.endpoints_distinct

end NoExoticSixSphere.CurveDecomposition
