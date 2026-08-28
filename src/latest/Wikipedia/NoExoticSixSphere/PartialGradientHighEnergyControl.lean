import Wikipedia.NoExoticSixSphere.PartialGradientLocalCrossing

/-!
# Small movement when a crossing loses little energy

The spatial tolerance determines an energy window, not a smaller initial
crossing domain. The avoidance energy increase can then be chosen arbitrarily
small within that window. This order of quantifiers is suited to a fixed finite
cover of critical points.
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

theorem exists_small_energy_loss_crossing (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ ζ > 0, ∀ (r : ℝ), 0 < r → Metric.ball (0 : E) (3 * r) ⊆ C.chart.source →
      ∀ (δ l k e : ℝ), l < k →
        (∀ z ∈ C.radialDomain r, f (C.radial r (1, z)) ≤ f (C.center z) - δ) →
        ∀ (ξ : ℝ), 0 < ξ → ξ ≤ ζ →
          ∀ (p : C(M, E)), (∀ x, p x ∈ C.crossingDomain r l (k + δ) e) →
            ∀ (S : Set M), IsCompact S → (∀ x ∈ S, f (p x) ≤ l) →
              finrank ℝ B < finrank ℝ D →
              ∃ q : C(M, E), (∀ x, f (q x) < k) ∧
                ∃ G : ContinuousMap.HomotopyRel p q S,
                  ∀ t x, G (t, x) ∈ C.chart.source ∧ f (G (t, x)) < e ∧
                    ‖G (t, x)‖ < 2 * r ∧ f (G (t, x)) < f (p x) + ξ ∧
                    (f (p x) - f (G (t, x)) ≤ 2 * ζ → dist (G (t, x)) (p x) < ρ) := by
  obtain ⟨c, hc, hcost⟩ := C.exists_radial_displacement_bound hU hf
  let ζ := c * ρ ^ 2 / 16
  have hcρ : 0 < c * ρ ^ 2 := mul_pos hc (sq_pos_of_pos hρ)
  refine ⟨ζ, by dsimp [ζ]; positivity, ?_⟩
  intro r hr hball δ l k e hlk hgap ξ hξ hξω p hp S hS hLow hd
  obtain ⟨q, hq, G, hG⟩ := C.exists_crossing_homotopy_with_cost (I := I) hU hf r hr hball
    c hc (hcost r hr hball) (ρ / 4) ξ (by positivity) hξ δ l k e hlk hgap p hp S hS hLow hd
  refine ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1, (hG t x).2.2.1,
    (hG t x).2.2.2.2.2.1, ?_⟩⟩
  intro hsmall
  have hh := (hG t x).2.2.2.2.2.2
  by_contra hn
  have hlarge : ρ ≤ dist (G (t, x)) (p x) := le_of_not_gt hn
  have hsquare := pow_le_pow_left₀ hρ.le hlarge 2
  have hbound := mul_le_mul_of_nonneg_left hsquare (by linarith : 0 ≤ c / 2)
  have hmargin : c * (ρ / 4) ^ 2 + 3 * ζ < (c / 2) * ρ ^ 2 := by
    dsimp [ζ]
    nlinarith
  linarith

theorem exists_quantitative_crossing_neighborhood (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (N : Set E) (hN : IsOpen N) (hNzero : (0 : E) ∈ N)
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B < finrank ℝ D) :
    ∃ r > 0, ∃ V : Set E,
      IsOpen V ∧ (0 : E) ∈ V ∧ V ⊆ C.chart.source ∩ N ∧
      (∀ z ∈ V, ‖z‖ < 2 * r) ∧
      ∃ l k : ℝ, l < k ∧ k < f 0 ∧
        ∀ ρ > 0, ∃ ζ > 0, ∀ ξ : ℝ, 0 < ξ → ξ ≤ ζ →
          ∀ (p : C(M, E)), (∀ x, p x ∈ V) →
            ∀ (S : Set M), IsCompact S → (∀ x ∈ S, f (p x) ≤ l) →
              ∃ q : C(M, E), (∀ x, f (q x) < k) ∧
                ∃ G : ContinuousMap.HomotopyRel p q S,
                  ∀ t x, G (t, x) ∈ C.chart.source ∧ f (G (t, x)) < f 0 + ε ∧
                    ‖G (t, x)‖ < 2 * r ∧ G (t, x) ∈ N ∧ f (G (t, x)) < f (p x) + ξ ∧
                    (f (p x) - f (G (t, x)) ≤ 2 * ζ → dist (G (t, x)) (p x) < ρ) := by
  obtain ⟨a, ha, haball⟩ := Metric.mem_nhds_iff.mp
    ((C.chart.open_source.inter hN).mem_nhds ⟨C.zero_mem_source, hNzero⟩)
  let r := a / 4
  have hr : 0 < r := by dsimp [r]; positivity
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
  refine ⟨r, hr, V, C.isOpen_crossingDomain hU hf.continuousOn _ _ _ _,
    C.zero_mem_crossingDomain _ _ _ _ hr (by dsimp [l]; linarith)
      (by dsimp [k]; linarith) (by linarith),
    (fun z hz ↦ hsmall (C.norm_lt_of_mem_crossingDomain _ _ _ _ hz)),
    (fun z hz ↦ C.norm_lt_of_mem_crossingDomain _ _ _ _ hz), l, k, hlk,
    (by dsimp [k]; linarith), ?_⟩
  intro ρ hρ
  obtain ⟨ζ, hζ, hcross⟩ := C.exists_small_energy_loss_crossing (I := I) (M := M) hU hf ρ hρ
  refine ⟨ζ, hζ, ?_⟩
  intro ξ hξ hξζ p hp S hS hLow
  obtain ⟨q, hq, G, hG⟩ := hcross r hr hball δ l k (f 0 + ε) hlk hgap
    ξ hξ hξζ p hp S hS hLow hd
  exact ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1, (hG t x).2.2.1,
    (hsmall (hG t x).2.2.1).2, (hG t x).2.2.2.1, (hG t x).2.2.2.2⟩⟩

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
