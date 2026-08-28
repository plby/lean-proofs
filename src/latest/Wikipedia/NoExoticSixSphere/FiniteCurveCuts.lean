import Wikipedia.NoExoticSixSphere.FiniteCurveIntervalCover

/-!
# The finite cut set from the interval cover

Both endpoints of every selected compact arc are retained as actual points
of the original space. This finite set contains all the chart-region frontiers
and the zero-coordinate boundary. No edge or incidence count is assumed.
-/

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

variable {X ι : Type*} [TopologicalSpace X]

def cutSet (t : Finset ι) (N : ι → IntervalNeighborhood X) : Set X :=
  ⋃ i ∈ t, (N i).endpoints

theorem finite_cutSet (t : Finset ι) (N : ι → IntervalNeighborhood X) :
    (cutSet t N).Finite :=
  t.finite_toSet.biUnion (fun i _ ↦
    (finite_singleton ((N i).chart.symm (N i).right)).insert ((N i).chart.symm (N i).left))

theorem endpoints_subset_cutSet (t : Finset ι) (N : ι → IntervalNeighborhood X)
    {i : ι} (hi : i ∈ t) : (N i).endpoints ⊆ cutSet t N :=
  fun _ hx ↦ mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hx⟩⟩

theorem frontier_subset_cutSet [T2Space X] (t : Finset ι) (N : ι → IntervalNeighborhood X)
    {i : ι} (hi : i ∈ t) : frontier (N i).openSet ⊆ cutSet t N :=
  (N i).frontier_subset_endpoints.trans (endpoints_subset_cutSet t N hi)

theorem boundary_subset_cutSet (t : Finset ι) (N : ι → IntervalNeighborhood X)
    (hcov : univ ⊆ ⋃ i ∈ t, (N i).openSet) (B : Set X)
    (hB : ∀ i ∈ t, ∀ y ∈ (N i).chart.source, ((N i).chart y).val = 0 ↔ y ∈ B) :
    B ⊆ cutSet t N := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcov (mem_univ x))
  exact endpoints_subset_cutSet t N hi ((N i).boundary_mem_endpoints B (hB i hi) hxi hx)

end NoExoticSixSphere.CurveDecomposition
