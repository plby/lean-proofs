import Wikipedia.NoExoticSixSphere.PartialGradientCoreCrossing
import Wikipedia.NoExoticSixSphere.PartialGradientCompactCore
import Wikipedia.NoExoticSixSphere.LocalCoreClearing

/-!
# Clearing a fiber core of high-energy points

Combine the controlled local crossing with compact fiber cores and localization.
The outer core and localization neighborhood are independent of the avoidance
tolerance. An arbitrary admissible family is changed only inside that
neighborhood. Its endpoint has no point of energy at least `k` in the inner core.
-/

open Set Module
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {B H M D E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

include I

theorem exists_localized_core_crossing (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (r : ℝ) (hr : 0 < r) (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source)
    (δ l k e : ℝ) (hlk : l < k)
    (hgap : ∀ z ∈ C.radialDomain r, f (C.radial r (1, z)) ≤ f (C.center z) - δ)
    (hzero : (0 : E) ∈ C.crossingDomain r l (k + δ) e)
    (hd : finrank ℝ B < finrank ℝ D) :
    ∃ (V : Set E) (a b : ℝ),
      IsOpen V ∧ (0 : E) ∈ V ∧ V ⊆ C.crossingDomain r l (k + δ) e ∧
      0 < a ∧ 0 < b ∧ IsCompact (closure (C.fiberCore a b)) ∧
      closure (C.fiberCore a b) ⊆ V ∧
      ∀ η : ℝ, 0 < η → η < b →
        (0 : E) ∈ C.fiberCore a (b - η) ∧
        ∀ (p : C(M, E)), (∀ x, p x ∈ C.chart.source) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, f (p x) ≤ l) →
            ∃ q : C(M, E),
              (∀ x, p x ∈ closure (C.fiberCore a b) → f (q x) < k) ∧
              (∀ x, k ≤ f (q x) → q x ∉ C.fiberCore a (b - η)) ∧
              ∃ G : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                ∀ t x, G (t, x) ∈ C.chart.source ∧
                  f (G (t, x)) ≤ max (f (p x)) e ∧
                  (p x ∉ closure (C.fiberCore a b) → G (t, x) ∉ C.fiberCore a (b - η)) := by
  obtain ⟨V, hV, hVzero, hVW, hclear⟩ := exists_core_clearing_neighborhood (M := M)
    (OpenPartialHomeomorph.refl E) continuous_id (mem_univ (0 : E))
    (C.crossingDomain r l (k + δ) e)
    (C.isOpen_crossingDomain hU hf.continuousOn r l (k + δ) e) hzero
  obtain ⟨a, b, ha, hb, hcompact, hcoreV⟩ := C.exists_compact_fiberCore_in V hV hVzero
  refine ⟨V, a, b, hV, hVzero, hVW, ha, hb, hcompact, hcoreV, ?_⟩
  intro η hη hηb
  refine ⟨C.zero_mem_fiberCore ha (sub_pos.mpr hηb), ?_⟩
  apply hclear f C.chart.source (closure (C.fiberCore a b)) (C.fiberCore a (b - η))
    l k e hcompact hcoreV
    ((C.fiberCore_mono le_rfl (sub_le_self b hη.le)).trans subset_closure)
  intro p hp S hS hLow
  obtain ⟨q, hq, G, hG⟩ := C.exists_core_nonentering_crossing (I := I)
    hU hf r hr hball a b η hη δ l k e hlk hgap p hp S hS hLow hd
  exact ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1,
    fun hx ↦ (hG t x).2.2 (fun hi ↦ hx (subset_closure hi))⟩⟩

theorem exists_core_clearing (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B < finrank ℝ D) :
    ∃ V outer inner : Set E,
      IsOpen V ∧ (0 : E) ∈ V ∧ V ⊆ C.chart.source ∧
      IsCompact outer ∧ outer ⊆ V ∧
      IsOpen inner ∧ (0 : E) ∈ inner ∧ inner ⊆ outer ∧
      ∃ l k : ℝ, l < k ∧ k < f 0 ∧
        ∀ (p : C(M, E)), (∀ x, p x ∈ C.chart.source) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, f (p x) ≤ l) →
            ∃ q : C(M, E), (∀ x, p x ∈ outer → f (q x) < k) ∧
              (∀ x, k ≤ f (q x) → q x ∉ inner) ∧
              ∃ G : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                ∀ t x, G (t, x) ∈ C.chart.source ∧
                  f (G (t, x)) ≤ max (f (p x)) (f 0 + ε) ∧
                  (p x ∉ outer → G (t, x) ∉ inner) := by
  obtain ⟨r, hr, hball⟩ := C.exists_radial_radius
  obtain ⟨δ, hδ, hgap⟩ := C.exists_radial_endpoint_gap hU hf r hr hball
  let l := f 0 - 3 * δ / 4
  let k := f 0 - δ / 2
  have hlk : l < k := by dsimp [l, k]; linarith
  have hzero := C.zero_mem_crossingDomain r l (k + δ) (f 0 + ε) hr
    (by dsimp [l]; linarith) (by dsimp [k]; linarith) (by linarith)
  obtain ⟨V, a, b, hV, hVzero, hVW, ha, hb, hcompact, hcoreV, hclear⟩ :=
    C.exists_localized_core_crossing (I := I) (M := M) hU hf r hr hball
      δ l k (f 0 + ε) hlk hgap hzero hd
  obtain ⟨hinnerzero, hcross⟩ := hclear (b / 2) (by positivity) (by linarith)
  refine ⟨V, closure (C.fiberCore a b), C.fiberCore a (b - b / 2), hV, hVzero,
    hVW.trans (C.crossingDomain_subset_source r l (k + δ) (f 0 + ε)),
    hcompact, hcoreV, C.isOpen_fiberCore _ _, hinnerzero,
    (C.fiberCore_mono le_rfl ?_).trans subset_closure, l, k, hlk, ?_, hcross⟩
  · linarith
  · dsimp [k]
    linarith

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
