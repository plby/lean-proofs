import Wikipedia.NoExoticSixSphere.PartialGradientCoreClearing

/-!
# Core clearing for arbitrary families in a charted target

The local analytic data live in a real normed coordinate space, while the
parameter family need not lie in the target chart. Compact coordinate cores
are transported to the target before applying the supported localization.
Moved points remain in any prescribed neighborhood of the chart center.
-/

open Set Module
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {B H M D E Y : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace Y] [T2Space Y]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

include I

theorem exists_core_clearing_in_chart (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (e : OpenPartialHomeomorph Y E) (hinv : Continuous e.symm)
    (hzero : (0 : E) ∈ e.target) (energy : Y → ℝ)
    (henergy : ∀ z, f z = energy (e.symm z))
    (admissible : Set Y) (hadm : C.chart.source ⊆ e.symm ⁻¹' admissible)
    (N : Set Y) (hN : IsOpen N) (hcenter : e.symm 0 ∈ N)
    (ε : ℝ) (hε : 0 < ε) (hd : finrank ℝ B < finrank ℝ D) :
    ∃ V outer inner : Set Y,
      IsOpen V ∧ e.symm 0 ∈ V ∧ V ⊆ admissible ∩ N ∧
      IsCompact outer ∧ outer ⊆ V ∧
      IsOpen inner ∧ e.symm 0 ∈ inner ∧ inner ⊆ outer ∧
      ∃ l k : ℝ, l < k ∧ k < energy (e.symm 0) ∧
        ∀ (p : C(M, Y)), (∀ x, p x ∈ admissible) →
          ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy (p x) ≤ l) →
            ∃ q : C(M, Y), (∀ x, p x ∈ outer → energy (q x) < k) ∧
              (∀ x, k ≤ energy (q x) → q x ∉ inner) ∧
              ∃ G : ContinuousMap.HomotopyRel p q (S ∪ (p ⁻¹' V)ᶜ),
                ∀ t x, G (t, x) ∈ admissible ∧
                  energy (G (t, x)) ≤ max (energy (p x)) (energy (e.symm 0) + ε) ∧
                  (G (t, x) = p x ∨ G (t, x) ∈ N) ∧
                  (p x ∉ outer → G (t, x) ∉ inner) := by
  obtain ⟨s, hs, hsball⟩ := Metric.mem_nhds_iff.mp
    ((C.chart.open_source.inter (e.open_target.inter (hN.preimage hinv))).mem_nhds
      ⟨C.zero_mem_source, hzero, hcenter⟩)
  let r := s / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source :=
    ((Metric.ball_subset_ball (by dsimp [r]; linarith)).trans hsball).trans inter_subset_left
  have hsmall {z : E} (hz : ‖z‖ < 2 * r) :
      z ∈ C.chart.source ∧ z ∈ e.target ∧ e.symm z ∈ N := by
    apply hsball
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r] at hz
    linarith
  obtain ⟨δ, hδ, hgap⟩ := C.exists_radial_endpoint_gap hU hf r hr hball
  let l := f 0 - 3 * δ / 4
  let k := f 0 - δ / 2
  have hlk : l < k := by dsimp [l, k]; linarith
  let W₀ := C.crossingDomain r l (k + δ) (f 0 + ε)
  have hW₀ : IsOpen W₀ := C.isOpen_crossingDomain hU hf.continuousOn _ _ _ _
  have hW₀zero : (0 : E) ∈ W₀ := C.zero_mem_crossingDomain _ _ _ _ hr
    (by dsimp [l]; linarith) (by dsimp [k]; linarith) (by linarith)
  let W := e.source ∩ e ⁻¹' W₀
  have hW : IsOpen W := e.isOpen_inter_preimage hW₀
  have hWcenter : e.symm 0 ∈ W := ⟨e.map_target hzero, by
    change e (e.symm 0) ∈ W₀
    rwa [e.right_inv hzero]⟩
  have hWsub : W ⊆ admissible ∩ N := by
    intro y hy
    have hh := hsmall (C.norm_lt_of_mem_crossingDomain _ _ _ _ hy.2)
    have ha := hadm hh.1
    change e.symm (e y) ∈ admissible at ha
    rw [e.left_inv hy.1] at ha
    have hn := hh.2.2
    rw [e.left_inv hy.1] at hn
    exact ⟨ha, hn⟩
  obtain ⟨V, hV, hVcenter, hVW, hclear⟩ :=
    exists_controlled_core_clearing_neighborhood (M := M) e hinv hzero W hW hWcenter
  obtain ⟨a, b, ha, hb, hcompact, hcore⟩ := C.exists_compact_fiberCore_in
    (e.target ∩ e.symm ⁻¹' V) (e.open_target.inter (hV.preimage hinv)) ⟨hzero, hVcenter⟩
  let outer := e.symm '' closure (C.fiberCore a b)
  let inner := e.source ∩ e ⁻¹' C.fiberCore a (b - b / 2)
  have houter : IsCompact outer := hcompact.image hinv
  have houterV : outer ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hcore hz).2
  have hinner : IsOpen inner := e.isOpen_inter_preimage (C.isOpen_fiberCore _ _)
  have hinnercenter : e.symm 0 ∈ inner := ⟨e.map_target hzero, by
    change e (e.symm 0) ∈ C.fiberCore a (b - b / 2)
    rw [e.right_inv hzero]
    exact C.zero_mem_fiberCore ha (by linarith)⟩
  have hinnerouter : inner ⊆ outer := by
    intro y hy
    exact ⟨e y, subset_closure (C.fiberCore_mono le_rfl (by linarith) hy.2), e.left_inv hy.1⟩
  refine ⟨V, outer, inner, hV, hVcenter, hVW.trans hWsub, houter, houterV,
    hinner, hinnercenter, hinnerouter, l, k, hlk, ?_, ?_⟩
  · rw [← henergy 0]
    dsimp [k]
    linarith
  apply hclear energy admissible outer inner N l k (energy (e.symm 0) + ε)
    houter houterV hinnerouter
  intro p hp S hS hLow
  let p' : C(M, E) := ⟨fun x ↦ e (p x),
    e.continuousOn.comp_continuous p.continuous (fun x ↦ (hp x).1)⟩
  have hp' : ∀ x, p' x ∈ W₀ := fun x ↦ (hp x).2
  have hLow' : ∀ x ∈ S, f (p' x) ≤ l := by
    intro x hx
    rw [henergy]
    change energy (e.symm (e (p x))) ≤ l
    rw [e.left_inv (hp x).1]
    exact hLow x hx
  obtain ⟨q', hq', G', hG'⟩ := C.exists_crossing_homotopy_with_fiber_control (I := I)
    hU hf r hr hball (b / 2) (by positivity) δ l k (f 0 + ε) hlk hgap p' hp' S hS hLow' hd
  let inverse : C(E, Y) := ⟨e.symm, hinv⟩
  have hround : inverse.comp p' = p :=
    ContinuousMap.ext (fun x ↦ e.left_inv (hp x).1)
  let G : ContinuousMap.HomotopyRel p (inverse.comp q') S :=
    (G'.compContinuousMap inverse).cast hround rfl
  refine ⟨inverse.comp q', ?_, G, fun t x ↦ ?_⟩
  · intro x
    change energy (e.symm (q' x)) < k
    rw [← henergy]
    exact hq' x
  have hh := hG' t x
  have hs' := hsmall hh.2.2.1
  refine ⟨hadm hh.1, ?_, hs'.2.2, ?_⟩
  · change energy (e.symm (G' (t, x))) < energy (e.symm 0) + ε
    rw [← henergy, ← henergy]
    exact hh.2.1
  intro hout hnew
  have hout' : p' x ∉ C.fiberCore a b := by
    intro hz
    apply hout
    exact ⟨p' x, subset_closure hz, e.left_inv (hp x).1⟩
  have hno := C.notMem_fiberCore_of_control (hp' x).1 hout' hh.2.2.2.1 hh.2.2.2.2
  apply hno
  have hz : e (e.symm (G' (t, x))) ∈ C.fiberCore a (b - b / 2) := hnew.2
  rwa [e.right_inv hs'.2.1] at hz

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
