import Wikipedia.NoExoticSixSphere.PartialGradientLocalCrossing

/-!
# Keeping a local crossing in a prescribed neighborhood

The radial radius can be chosen small enough that both the avoidance stage and
the radial stage stay in any prescribed open neighborhood of the origin. The
energy and relative conditions of the crossing are preserved.
-/

open Set Module
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {B H M D E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

include I

theorem exists_crossing_in_neighborhood (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (N : Set E) (hN : IsOpen N) (hNzero : (0 : E) ∈ N)
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B < finrank ℝ D) :
    ∃ V : Set E, IsOpen V ∧ (0 : E) ∈ V ∧ V ⊆ C.chart.source ∩ N ∧
      ∃ l k : ℝ, l < k ∧ k < f 0 ∧
        ∀ (p : C(M, E)), (∀ x, p x ∈ V) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, f (p x) ≤ l) →
            ∃ q : C(M, E), (∀ x, f (q x) < k) ∧
              ∃ G : ContinuousMap.HomotopyRel p q S,
                ∀ t x, G (t, x) ∈ C.chart.source ∧ f (G (t, x)) < f 0 + ε ∧ G (t, x) ∈ N := by
  obtain ⟨a, ha, haball⟩ := Metric.mem_nhds_iff.mp
    ((C.chart.open_source.inter hN).mem_nhds ⟨C.zero_mem_source, hNzero⟩)
  let r := a / 4
  have hr : 0 < r := by dsimp [r]; linarith
  have hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source :=
    ((Metric.ball_subset_ball (by dsimp [r]; linarith)).trans haball).trans inter_subset_left
  have hsmall {z : E} (hz : ‖z‖ < 2 * r) : z ∈ C.chart.source ∩ N := by
    apply haball
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r] at hz
    linarith
  obtain ⟨δ, hδ, hgap⟩ := C.exists_radial_endpoint_gap hU hf r hr hball
  let l := f 0 - 3 * δ / 4
  let k := f 0 - δ / 2
  have hlk : l < k := by dsimp [l, k]; linarith
  let V := C.crossingDomain r l (k + δ) (f 0 + ε)
  refine ⟨V, C.isOpen_crossingDomain hU hf.continuousOn r l (k + δ) (f 0 + ε),
    C.zero_mem_crossingDomain r l (k + δ) (f 0 + ε) hr
      (by dsimp [l]; linarith) (by dsimp [k]; linarith) (by linarith),
    (fun z hz ↦ hsmall (C.norm_lt_of_mem_crossingDomain r l (k + δ) (f 0 + ε) hz)),
    l, k, hlk, (by dsimp [k]; linarith), ?_⟩
  intro p hp S hS hLow
  obtain ⟨q, hq, G, hG⟩ := C.exists_crossing_homotopy_with_norm (I := I) hU hf r hr hball
    δ l k (f 0 + ε) hlk hgap p hp S hS hLow hd
  exact ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1, (hsmall (hG t x).2.2).2⟩⟩

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
