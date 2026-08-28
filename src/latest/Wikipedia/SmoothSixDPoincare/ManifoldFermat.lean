import Wikipedia.SmoothSixDPoincare.ManifoldCriticalPoints
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Fermat's theorem for the native manifold derivative

An extremum in the original manifold topology remains an extremum in a
genuine smooth chart. Euclidean Fermat then proves that the native
manifold derivative vanishes.
-/

noncomputable section

open Set Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {p : M}

/-- A local minimum is a critical point for the actual native manifold derivative. -/
theorem mem_criticalPoints_of_localMin
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hmin : IsLocalMin f p) :
    p ∈ criticalPoints E f := by
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hp : p ∈ e.source := mem_chart_source E p
  apply (mem_criticalPoints_iff hf he hp).mpr
  have hmin' : IsLocalMin f (e.symm (e p)) := by rw [e.left_inv hp]; exact hmin
  exact (hmin'.comp_continuous (e.continuousAt_symm (e.map_source hp))).fderiv_eq_zero

/-- A local maximum is a critical point for the actual native manifold derivative. -/
theorem mem_criticalPoints_of_localMax
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hmax : IsLocalMax f p) :
    p ∈ criticalPoints E f := by
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hp : p ∈ e.source := mem_chart_source E p
  apply (mem_criticalPoints_iff hf he hp).mpr
  have hmax' : IsLocalMax f (e.symm (e p)) := by rw [e.left_inv hp]; exact hmax
  exact (hmax'.comp_continuous (e.continuousAt_symm (e.map_source hp))).fderiv_eq_zero

variable [CompactSpace M]

/-- With just two possible critical points at distinct ordered values, they are the unique global
minimum and maximum. No extremum or disk description is postulated. -/
theorem unique_extrema_of_two_critical_values
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {p q : M} (hpq : f p < f q)
    (hcrit : ∀ x ∈ criticalPoints E f, x = p ∨ x = q) :
    (∀ x, f x ≤ f p → x = p) ∧ (∀ x, f q ≤ f x → x = q) := by
  obtain ⟨u, _, hmin⟩ := isCompact_univ.exists_isMinOn ⟨p, mem_univ p⟩ hf.continuous.continuousOn
  obtain ⟨v, _, hmax⟩ := isCompact_univ.exists_isMaxOn ⟨q, mem_univ q⟩ hf.continuous.continuousOn
  have humin : IsLocalMin f u := Filter.Eventually.of_forall (fun x => hmin (mem_univ x))
  have hvmax : IsLocalMax f v := Filter.Eventually.of_forall (fun x => hmax (mem_univ x))
  have hup : u = p := by
    rcases hcrit u (mem_criticalPoints_of_localMin hf humin) with h | h
    · exact h
    · have hle : f u ≤ f p := hmin (mem_univ p)
      rw [h] at hle
      exact False.elim (not_le_of_gt hpq hle)
  have hvq : v = q := by
    rcases hcrit v (mem_criticalPoints_of_localMax hf hvmax) with h | h
    · have hle : f q ≤ f v := hmax (mem_univ q)
      rw [h] at hle
      exact False.elim (not_le_of_gt hpq hle)
    · exact h
  have hglobalMin (x : M) : f p ≤ f x := by rw [← hup]; exact hmin (mem_univ x)
  have hglobalMax (x : M) : f x ≤ f q := by rw [← hvq]; exact hmax (mem_univ x)
  constructor
  · intro x hx
    have hlocal : IsLocalMin f x := Filter.Eventually.of_forall (fun y => hx.trans (hglobalMin y))
    rcases hcrit x (mem_criticalPoints_of_localMin hf hlocal) with h | h
    · exact h
    · rw [h] at hx
      exact False.elim (not_le_of_gt hpq hx)
  · intro x hx
    have hlocal : IsLocalMax f x := Filter.Eventually.of_forall (fun y => (hglobalMax y).trans hx)
    rcases hcrit x (mem_criticalPoints_of_localMax hf hlocal) with h | h
    · rw [h] at hx
      exact False.elim (not_le_of_gt hpq hx)
    · exact h

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
