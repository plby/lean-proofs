import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Metrizable.Urysohn

/-! # Open continuity neighborhoods and compact continuity cores -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory TopologicalSpace

theorem exists_open_null_boundary_neighborhood {X : Type*} [TopologicalSpace X]
    [MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [SFinite μ] {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ μ (frontier V) = 0 := by
  letI : MetricSpace X := metrizableSpaceMetric X
  obtain ⟨δ, hδ, hsub⟩ := isCompact_singleton.exists_thickening_subset_open hU
    (Set.singleton_subset_iff.mpr hx)
  obtain ⟨r, hr, hnull⟩ := exists_null_frontier_thickening μ ({x} : Set X) hδ
  refine ⟨Metric.thickening r {x}, Metric.isOpen_thickening, ?_, ?_, hnull⟩
  · exact Metric.self_subset_thickening hr.1 _ (Set.mem_singleton x)
  · exact (Metric.thickening_mono hr.2.le _).trans hsub

theorem exists_open_compact_null_boundary_superset {X : Type*} [TopologicalSpace X]
    [MetrizableSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [SFinite μ] {K : Set X} (hK : IsCompact K) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ IsCompact (closure U) ∧ μ (frontier U) = 0 := by
  letI : MetricSpace X := metrizableSpaceMetric X
  obtain ⟨δ, hδ, hcompact⟩ := hK.exists_isCompact_cthickening
  obtain ⟨r, hr, hnull⟩ := exists_null_frontier_thickening μ K hδ
  refine ⟨Metric.thickening r K, Metric.isOpen_thickening,
    Metric.self_subset_thickening hr.1 K, ?_, hnull⟩
  exact hcompact.of_isClosed_subset isClosed_closure
    ((Metric.closure_thickening_subset_cthickening r K).trans (Metric.cthickening_mono hr.2.le K))

end Erdos1148.DukeArithmetic
