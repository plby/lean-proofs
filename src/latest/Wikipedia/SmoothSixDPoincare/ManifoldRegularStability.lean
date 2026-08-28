import Wikipedia.SmoothSixDPoincare.ManifoldCriticalPoints

/-!
# Stability of the native regular locus in a smooth family

The nonzero native-derivative condition is open in parameter and point.
Consequently, a compact regular region remains regular for nearby
parameters. This controls the creation of new critical points when
separating critical values by localized constant perturbations.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E P M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Nonvanishing of the coordinate derivative is open in any fixed smooth chart. -/
theorem isOpen_regularInChart {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f))
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    IsOpen {q : P × M | q.2 ∈ e.source ∧ fderiv ℝ (f q.1 ∘ e.symm) (e q.2) ≠ 0} := by
  have hU : IsOpen {q : P × E | q.2 ∈ e.target} := e.open_target.preimage continuous_snd
  have hd := MorsePerturbation.contDiffOn_spatialDerivative
    (f := fun a y => f a (e.symm y)) hU (contDiffOn_inChart hf he)
  have hg := hd.continuousOn.isOpen_inter_preimage hU
    (isClosed_singleton (x := (0 : E →L[ℝ] ℝ))).isOpen_compl
  let S : Set (P × M) := {q | q.2 ∈ e.source}
  have hS : IsOpen S := e.open_source.preimage continuous_snd
  have hm : ContinuousOn (fun q : P × M => (q.1, e q.2)) S :=
    continuous_fst.continuousOn.prodMk
      (e.continuousOn.comp continuous_snd.continuousOn (fun _ hq => hq))
  convert hm.isOpen_inter_preimage hS hg using 1
  ext q
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff, S]
  constructor
  · rintro ⟨hq, hn⟩
    exact ⟨hq, e.map_source hq, hn⟩
  · rintro ⟨hq, -, hn⟩
    exact ⟨hq, hn⟩

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual native regular locus of a jointly smooth family is open in parameter and point. -/
theorem isOpen_regularPoint {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f)) :
    IsOpen {q : P × M | q.2 ∉ criticalPoints E (f q.1)} := by
  have hslice (a : P) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (f a) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  rw [isOpen_iff_mem_nhds]
  intro q hq
  let e := chartAt E q.2
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas q.2
  have hx : q.2 ∈ e.source := mem_chart_source E q.2
  have hmem : q ∈ {r : P × M | r.2 ∈ e.source ∧ fderiv ℝ (f r.1 ∘ e.symm) (e r.2) ≠ 0} :=
    ⟨hx, fun hz => hq ((mem_criticalPoints_iff (hslice q.1) he hx).mpr hz)⟩
  apply mem_of_superset ((isOpen_regularInChart hf he).mem_nhds hmem)
  intro r hr hcrit
  exact hr.2 ((mem_criticalPoints_iff (hslice r.1) he hr.1).mp hcrit)

/-- A compact region with no native critical points stays regular for nearby parameters. -/
theorem isOpen_regularOn {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f))
    {K : Set M} (hK : IsCompact K) :
    IsOpen {a : P | ∀ x ∈ K, x ∉ criticalPoints E (f a)} :=
  MorsePerturbation.isOpen_forall_mem_compact hK (isOpen_regularPoint hf)

/-- If all critical points lie in an open region where the family's critical-point predicate is
unchanged, compact regular stability prevents the appearance of any new critical points. -/
theorem eventually_criticalPoints_eq [CompactSpace M] {f : P → M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry f))
    (a₀ : P) {U : Set M} (hU : IsOpen U) (hcover : criticalPoints E (f a₀) ⊆ U)
    (hfixed : ∀ a x, x ∈ U → (x ∈ criticalPoints E (f a) ↔ x ∈ criticalPoints E (f a₀))) :
    ∀ᶠ a in 𝓝 a₀, criticalPoints E (f a) = criticalPoints E (f a₀) := by
  have hreg : ∀ x ∈ Uᶜ, x ∉ criticalPoints E (f a₀) :=
    fun x hx hc => hx (hcover hc)
  have hn := (isOpen_regularOn hf hU.isClosed_compl.isCompact).mem_nhds hreg
  filter_upwards [hn] with a ha
  ext x
  by_cases hx : x ∈ U
  · exact hfixed a x hx
  · exact iff_of_false (ha x hx) (hreg x hx)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
