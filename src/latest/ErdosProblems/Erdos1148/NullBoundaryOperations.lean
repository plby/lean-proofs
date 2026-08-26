import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! # Null boundaries under finite intersections and invariant preimages -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

lemma frontier_finite_iInter_subset {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (s : ι → Set X) : frontier (⋂ i, s i) ⊆ ⋃ i, frontier (s i) := by
  classical
  intro x hx
  by_contra hnot
  have hcl (i : ι) : x ∈ closure (s i) :=
    closure_mono (Set.iInter_subset s i) hx.1
  have hint (i : ι) : x ∈ interior (s i) := by
    by_contra hi
    exact hnot (Set.mem_iUnion.mpr ⟨i, ⟨hcl i, hi⟩⟩)
  apply hx.2
  rw [interior_iInter_of_finite]
  exact Set.mem_iInter.mpr hint

theorem measure_frontier_finite_iInter_eq_zero {X ι : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [Finite ι] (μ : Measure X) (s : ι → Set X)
    (hnull : ∀ i, μ (frontier (s i)) = 0) : μ (frontier (⋂ i, s i)) = 0 :=
  measure_mono_null (frontier_finite_iInter_subset s) (measure_iUnion_null hnull)

theorem measure_frontier_preimage_eq_zero {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) {f : X → X}
    (hf : Continuous f) (hinv : Measure.map f μ = μ) {s : Set X}
    (hnull : μ (frontier s) = 0) : μ (frontier (f ⁻¹' s)) = 0 := by
  apply measure_mono_null (hf.frontier_preimage_subset s)
  rw [← Measure.map_apply hf.measurable isClosed_frontier.measurableSet, hinv, hnull]

theorem measure_frontier_inter_eq_zero {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure X) {s t : Set X}
    (hs : μ (frontier s) = 0) (ht : μ (frontier t) = 0) :
    μ (frontier (s ∩ t)) = 0 :=
  measure_mono_null (frontier_inter_subset s t)
    (measure_union_null (measure_mono_null Set.inter_subset_left hs)
      (measure_mono_null Set.inter_subset_right ht))

theorem measure_frontier_diff_eq_zero {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure X) {s t : Set X}
    (hs : μ (frontier s) = 0) (ht : μ (frontier t) = 0) :
    μ (frontier (s \ t)) = 0 := by
  rw [Set.sdiff_eq]
  apply measure_frontier_inter_eq_zero μ hs
  simpa only [frontier_compl] using ht

end Erdos1148.DukeArithmetic
