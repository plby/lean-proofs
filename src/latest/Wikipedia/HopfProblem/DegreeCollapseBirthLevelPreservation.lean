import Wikipedia.HopfProblem.DegreeCollapseIndexedMorseBirth
import Wikipedia.SmoothSixDPoincare.ManifoldFermat

/-!
# Lower levels are unchanged by a birth supported in a higher band

Compactness and the native Fermat theorem exclude a hidden excursion below
the lower band boundary: a minimum of the new function on the old closed
superlevel would be either on the unchanged boundary or a critical point.
The exact critical-set and germ formulas therefore give literal equality
of every lower level, without assuming a uniform value bound on the cutoff.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {f g : M → ℝ}

theorem superlevel_bound_of_critical_bound (hf : Continuous f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) {l : ℝ}
    (hboundary : ∀ y, f y = l → g y = l)
    (hcritical : ∀ y ∈ criticalPoints E g, l ≤ f y → l ≤ g y) :
    ∀ x, l ≤ f x → l ≤ g x := by
  intro x hx
  have hK : IsCompact {y : M | l ≤ f y} := (isClosed_le continuous_const hf).isCompact
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn ⟨x, hx⟩ hg.continuous.continuousOn
  have hgp : l ≤ g p := by
    by_cases hlt : l < f p
    · have hlocal : IsLocalMin g p := by
        filter_upwards [(isOpen_lt continuous_const hf).mem_nhds hlt] with y hy
        exact hmin hy.le
      exact hcritical p (mem_criticalPoints_of_localMin hg hlocal) hp
    · have heq : f p = l := le_antisymm (le_of_not_gt hlt) hp
      exact (hboundary p heq).ge
  exact hgp.trans (hmin hx)

theorem birth_preserves_lower_levels (hf : Continuous f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) {l : ℝ} {U : Set M} {p q : M}
    (hU : U ⊆ {y : M | l < f y})
    (hexterior : ∀ y, y ∉ U → g =ᶠ[𝓝 y] f)
    (hkeep : ∀ y ∈ criticalPoints E f, g =ᶠ[𝓝 y] f)
    (hcrit : ∀ y ∈ criticalPoints E g, y ∈ criticalPoints E f ∨ y = p ∨ y = q)
    (hp : l ≤ g p) (hq : l ≤ g q) {a : ℝ} (ha : a < l) :
    (∀ y, g y = a ↔ f y = a) ∧ (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) := by
  have hout (y : M) (hy : f y ≤ l) : y ∉ U := fun h => (hU h).not_ge hy
  have hbound : ∀ y, l ≤ f y → l ≤ g y := by
    apply superlevel_bound_of_critical_bound hf hg
    · intro y hy
      exact (hexterior y (hout y hy.le)).self_of_nhds.trans hy
    · intro y hy hfy
      rcases hcrit y hy with hold | rfl | rfl
      · rw [(hkeep y hold).self_of_nhds]
        exact hfy
      · exact hp
      · exact hq
  refine ⟨?_, fun y hy => hexterior y (hout y (hy.trans ha.le))⟩
  intro y
  constructor
  · intro hgy
    have hfy : f y ≤ l := by
      by_contra h
      have hh := hbound y (le_of_not_ge h)
      rw [hgy] at hh
      exact ha.not_ge hh
    exact ((hexterior y (hout y hfy)).self_of_nhds).symm.trans hgy
  · intro hfy
    exact (hexterior y (hout y (hfy ▸ ha.le))).self_of_nhds.trans hfy

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
