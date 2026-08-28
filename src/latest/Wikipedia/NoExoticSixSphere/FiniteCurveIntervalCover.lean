import Wikipedia.NoExoticSixSphere.CurveIntervalNeighborhood

/-!
# Finite covers by actual compact interval neighborhoods

Compactness selects finitely many of the constructed interval neighborhoods.
Their original atlas charts are retained, so a supplied zero-coordinate
boundary identification remains valid without changing the underlying space.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

open InvolutionQuotient

variable {X : Type*} [TopologicalSpace X]

theorem exists_finite_interval_cover [CompactSpace X]
    (e : X → OpenPartialHomeomorph X HalfLine) (he : ∀ x, x ∈ (e x).source) :
    ∃ N : X → IntervalNeighborhood X, ∃ t : Finset X,
      (∀ x, (N x).chart = e x) ∧ univ ⊆ ⋃ i ∈ t, (N i).openSet := by
  classical
  choose N hN hNx using fun x ↦ exists_interval_neighborhood (e x) x (he x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (N x).openSet)
    (fun x ↦ (N x).isOpen_openSet) (fun x _ ↦ mem_iUnion.mpr ⟨x, hNx x⟩)
  exact ⟨N, t, hN, ht⟩

theorem IntervalNeighborhood.boundary_mem_endpoints (d : IntervalNeighborhood X)
    (B : Set X) (hB : ∀ y ∈ d.chart.source, (d.chart y).val = 0 ↔ y ∈ B)
    {x : X} (hx : x ∈ d.openSet) (hxb : x ∈ B) : x ∈ d.endpoints := by
  have hz := (hB x hx.1).mpr hxb
  have hlo : d.left.val ≤ (d.chart x).val := (interior_subset hx.2).1
  have he : d.chart x = d.left := by
    apply Subtype.ext
    linarith [d.left.property]
  have hxe : x = d.chart.symm d.left := by
    rw [← he]
    exact (d.chart.left_inv hx.1).symm
  change x = d.chart.symm d.left ∨ x ∈ {d.chart.symm d.right}
  exact Or.inl hxe

theorem IntervalNeighborhood.endpoints_subset_closedSet (d : IntervalNeighborhood X) :
    d.endpoints ⊆ d.closedSet := by
  intro x hx
  rcases hx with hx | hx
  · exact ⟨d.left, ⟨le_rfl, d.lt.le⟩, hx.symm⟩
  · exact ⟨d.right, ⟨d.lt.le, le_rfl⟩, (mem_singleton_iff.mp hx).symm⟩

theorem IntervalNeighborhood.closedSet_sdiff_openSet_subset [T2Space X]
    (d : IntervalNeighborhood X) : d.closedSet \ d.openSet ⊆ d.endpoints := by
  have he : d.closedSet \ d.openSet = frontier d.openSet := by
    rw [frontier, d.isOpen_openSet.interior_eq, d.closure_openSet]
  rw [he]
  exact d.frontier_subset_endpoints

end NoExoticSixSphere.CurveDecomposition
