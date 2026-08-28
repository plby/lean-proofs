import Wikipedia.NoExoticSixSphere.CutCurveOpenComponents
import Wikipedia.NoExoticSixSphere.CompactConnectedChartInterval

/-!
# Nondegenerate interval closures of the actual cut-curve components

Each component closure stays inside one of the selected original charts.
Its actual real coordinate therefore identifies it with a compact interval.
The component is a nonempty open set, so that interval has distinct endpoints.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

open InvolutionQuotient

variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]

theorem exists_cutComponent_interval_in_chart (t : Finset ι) (N : ι → IntervalNeighborhood X)
    (hcov : univ ⊆ ⋃ i ∈ t, (N i).openSet) (x : {x : X // x ∉ cutSet t N}) :
    ∃ i ∈ t, closure (cutComponent (cutSet t N) x) ⊆ (N i).chart.source ∧
      ∃ a b : ℝ, a < b ∧
      ∃ h : closure (cutComponent (cutSet t N) x) ≃ₜ Icc a b,
        ∀ y, (h y).val = CurveChart.realCoordinate (N i).chart y.val := by
  obtain ⟨hcomp, i, hi, hs⟩ := compact_closure_cutComponent t N hcov x
  have hchart := hs.trans (N i).closedSet_subset_source
  obtain ⟨a, b, hab, h, hh⟩ := CurveChart.exists_interval_homeomorph (N i).chart
    (closure (cutComponent (cutSet t N) x)) hcomp
    (isConnected_cutComponent (cutSet t N) x).closure hchart
  have hn : ¬ (cutComponent (cutSet t N) x).Subsingleton :=
    CurveChart.not_subsingleton_of_open (N i).chart
      (isOpen_cutComponent (finite_cutSet t N).isClosed x)
      ⟨x.val, mem_cutComponent (cutSet t N) x⟩ (subset_closure.trans hchart)
  have hlt : a < b := by
    apply lt_of_le_of_ne hab
    intro he
    apply hn
    intro y hy z hz
    have hhy := (h ⟨y, subset_closure hy⟩).property
    have hhz := (h ⟨z, subset_closure hz⟩).property
    have heq : h ⟨y, subset_closure hy⟩ = h ⟨z, subset_closure hz⟩ := by
      apply Subtype.ext
      linarith [hhy.1, hhy.2, hhz.1, hhz.2]
    exact congrArg Subtype.val (h.injective heq)
  exact ⟨i, hi, hchart, a, b, hlt, h, hh⟩

theorem exists_cutComponent_interval (t : Finset ι) (N : ι → IntervalNeighborhood X)
    (hcov : univ ⊆ ⋃ i ∈ t, (N i).openSet) (x : {x : X // x ∉ cutSet t N}) :
    ∃ i ∈ t, ∃ a b : ℝ, a < b ∧
      ∃ h : closure (cutComponent (cutSet t N) x) ≃ₜ Icc a b,
        ∀ y, (h y).val = CurveChart.realCoordinate (N i).chart y.val := by
  obtain ⟨i, hi, hs, h⟩ := exists_cutComponent_interval_in_chart t N hcov x
  exact ⟨i, hi, h⟩

end NoExoticSixSphere.CurveDecomposition
