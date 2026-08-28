import Wikipedia.NoExoticSixSphere.CompactCurveBoundaryEven

/-!
# A compact Hausdorff half-line-charted space has finite even boundary

The boundary is specified by its actual zero-coordinate characterization in
every chart. Compactness constructs the finite interval cover; local
connectedness, the finite cuts and edges, and all incidence degrees are proved.
No finite decomposition or endpoint pairing is an input to this theorem.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

open InvolutionQuotient

theorem finite_even_boundary_of_compact_atlas {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] (B : Set X)
    (e : X → OpenPartialHomeomorph X HalfLine) (he : ∀ x, x ∈ (e x).source)
    (hB : ∀ x, ∀ y ∈ (e x).source, CurveChart.realCoordinate (e x) y = 0 ↔ y ∈ B) :
    B.Finite ∧ Even B.ncard := by
  let : ChartedSpace HalfLine X :=
    { atlas := range e
      chartAt := e
      mem_chart_source := he
      chart_mem_atlas := fun x ↦ ⟨x, rfl⟩ }
  let := chartedSpace_locallyConnected (X := X)
  obtain ⟨N, t, hN, hcov⟩ := exists_finite_interval_cover e he
  have hBN : ∀ i ∈ t, ∀ y ∈ (N i).chart.source,
      CurveChart.realCoordinate (N i).chart y = 0 ↔ y ∈ B := by
    intro i hi
    rw [hN i]
    exact hB i
  exact ⟨(finite_cutSet t N).subset (boundary_subset_cutSet t N hcov B hBN),
    even_boundary_of_finite_interval_cover t N hcov B hBN⟩

end NoExoticSixSphere.CurveDecomposition
