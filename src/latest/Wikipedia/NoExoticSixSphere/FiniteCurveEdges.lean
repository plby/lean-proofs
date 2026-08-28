import Wikipedia.NoExoticSixSphere.FiniteCurveIncidentComponents
import Wikipedia.NoExoticSixSphere.CutCurveOpenInterval

/-!
# The actual finite-cut curve has finitely many component edges

Each edge has a genuine marked endpoint in the finite cut set. At each cut,
the isolated-cut neighborhood bounds the incident edges by its local branches.
The finite union over the actual cuts therefore contains every actual edge.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]

theorem finite_incidentComponents_cutSet (t : Finset ι) (N : ι → IntervalNeighborhood X)
    (hcov : univ ⊆ ⋃ i ∈ t, (N i).openSet)
    (hzero : ∀ i ∈ t, ∀ y ∈ (N i).chart.source,
      CurveChart.realCoordinate (N i).chart y = 0 → y ∈ cutSet t N)
    (v : X) (hv : v ∈ cutSet t N) : (incidentComponents (cutSet t N) v).Finite := by
  obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.mp (hcov (mem_univ v))
  obtain ⟨d, hde, hvd, hcut⟩ := exists_interval_avoiding_other_cuts (cutSet t N)
    (finite_cutSet t N) (N i).chart v hvi.1
  apply d.finite_incidentComponents v hvd (cutSet t N) hv hcut
  intro y hy hz
  rw [hde] at hy hz
  exact hzero i hi y hy hz

theorem componentSet_subset_incident_union [LocallyConnectedSpace X]
    (t : Finset ι) (N : ι → IntervalNeighborhood X)
    (hcov : univ ⊆ ⋃ i ∈ t, (N i).openSet)
    (hzero : ∀ i ∈ t, ∀ y ∈ (N i).chart.source,
      CurveChart.realCoordinate (N i).chart y = 0 → y ∈ cutSet t N) :
    componentSet (cutSet t N) ⊆ ⋃ v ∈ cutSet t N, incidentComponents (cutSet t N) v := by
  rintro C ⟨x, rfl⟩
  obtain ⟨i, hi, m, hm⟩ := exists_cutComponent_marking t N hcov x
  have hz : ∀ y ∈ m.chart.source,
      CurveChart.realCoordinate m.chart y = 0 → y ∈ cutSet t N := by
    rw [hm]
    exact hzero i hi
  have hleft := m.leftPoint_mem_cuts (finite_cutSet t N).isClosed x hz
  exact mem_iUnion₂.mpr ⟨m.leftPoint.val, hleft, ⟨⟨x, rfl⟩, m.leftPoint.property⟩⟩

theorem finite_componentSet_cutSet [LocallyConnectedSpace X]
    (t : Finset ι) (N : ι → IntervalNeighborhood X)
    (hcov : univ ⊆ ⋃ i ∈ t, (N i).openSet)
    (hzero : ∀ i ∈ t, ∀ y ∈ (N i).chart.source,
      CurveChart.realCoordinate (N i).chart y = 0 → y ∈ cutSet t N) :
    (componentSet (cutSet t N)).Finite := by
  have hfin := (finite_cutSet t N).biUnion
    (fun v hv ↦ finite_incidentComponents_cutSet t N hcov hzero v hv)
  exact hfin.subset (componentSet_subset_incident_union t N hcov hzero)

end NoExoticSixSphere.CurveDecomposition
