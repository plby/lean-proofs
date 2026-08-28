import Wikipedia.NoExoticSixSphere.CurveEdgeEndpoints
import Wikipedia.NoExoticSixSphere.FiniteIncidenceParity

/-!
# The boundary of the actual finite-interval-covered curve has even cardinality

The finite cut set and finite edge set are constructed from the actual curve.
The proved local branches give degrees one and two, and the genuine interval
closures give two distinct endpoint cuts per edge. Double counting this actual
incidence relation proves evenness of the zero-coordinate boundary.
-/

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]

theorem even_boundary_of_finite_interval_cover (t : Finset ι)
    (N : ι → IntervalNeighborhood X) (hcov : univ ⊆ ⋃ i ∈ t, (N i).openSet) (B : Set X)
    (hB : ∀ i ∈ t, ∀ y ∈ (N i).chart.source,
      CurveChart.realCoordinate (N i).chart y = 0 ↔ y ∈ B) : Even B.ncard := by
  classical
  have hBS := boundary_subset_cutSet t N hcov B hB
  have hzero : ∀ i ∈ t, ∀ y ∈ (N i).chart.source,
      CurveChart.realCoordinate (N i).chart y = 0 → y ∈ cutSet t N :=
    fun i hi y hy hz ↦ hBS ((hB i hi y hy).mp hz)
  apply even_ncard_of_incidence (cutSet t N) (componentSet (cutSet t N))
    (finite_cutSet t N) (finite_componentSet_cutSet t N hcov hzero) B hBS
    (fun v C ↦ v ∈ closure C)
  · intro v hvB
    have h := incidentComponents_ncard_at_cut t N hcov B hB v (hBS hvB)
    simpa only [incidentComponents, if_pos hvB] using h
  · intro v hv hvB
    have h := incidentComponents_ncard_at_cut t N hcov B hB v hv
    simpa only [incidentComponents, if_neg hvB] using h
  · intro C hC
    exact edge_cut_intersection_ncard t N hcov hzero C hC

end NoExoticSixSphere.CurveDecomposition
