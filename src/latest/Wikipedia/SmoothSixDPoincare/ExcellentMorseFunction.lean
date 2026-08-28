import Wikipedia.SmoothSixDPoincare.SeparateCriticalValue
import Wikipedia.SmoothSixDPoincare.GlobalMorseFunction

/-!
# Smooth Morse functions with pairwise distinct critical values

Finite induction separates the critical values one at a time while
preserving the entire native critical-point set. Combining this with the
global Morse construction gives a function whose critical points can each
be treated by the isolated-critical-band attachment theorem.
-/

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- All critical values can be separated without changing any native critical point. -/
theorem exists_distinct_critical_values {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      criticalPoints E g = criticalPoints E f ∧ InjOn g (criticalPoints E g) := by
  classical
  let K := criticalPoints E f
  have hK : K.Finite := finite_criticalPoints hf hm
  have hfinite : ∀ s : Finset M, (s : Set M) ⊆ K →
      ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
        criticalPoints E g = K ∧ InjOn g (s : Set M) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨f, hf, hm, rfl, by simp⟩
    | @insert p s hps ih =>
      intro hsK
      have hsK' : (s : Set M) ⊆ K := fun x hx => hsK (Finset.mem_insert_of_mem hx)
      obtain ⟨g, hg, hmg, hcrit, hinj⟩ := ih hsK'
      obtain ⟨g', hg', hmg', hcrit', hfixed, hunique⟩ := exists_separating_critical_value hg hmg p
      have hK' : criticalPoints E g' = K := hcrit'.trans hcrit
      refine ⟨g', hg', hmg', hK', ?_⟩
      intro x hx y hy heq
      have hxcrit : x ∈ criticalPoints E g := hcrit ▸ hsK hx
      have hycrit : y ∈ criticalPoints E g := hcrit ▸ hsK hy
      by_cases hxp : x = p
      · subst x
        exact (hunique y hycrit heq.symm).symm
      by_cases hyp : y = p
      · subst y
        exact hunique x hxcrit heq
      have hxs : x ∈ (s : Set M) := (Finset.mem_insert.mp hx).resolve_left hxp
      have hys : y ∈ (s : Set M) := (Finset.mem_insert.mp hy).resolve_left hyp
      apply hinj hxs hys
      rw [← hfixed x hxcrit hxp, ← hfixed y hycrit hyp]
      exact heq
  obtain ⟨g, hg, hmg, hcrit, hinj⟩ := hfinite hK.toFinset (by simp)
  refine ⟨g, hg, hmg, hcrit, ?_⟩
  rw [hcrit]
  simpa only [hK.coe_toFinset] using hinj

variable (E M) in
/-- Every compact smooth manifold has a Morse function with distinct native critical values. -/
theorem exists_morse_function_with_distinct_critical_values :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      (criticalPoints E f).Finite ∧ InjOn f (criticalPoints E f) := by
  obtain ⟨f, hf, hm⟩ := exists_morse_function E M
  obtain ⟨g, hg, hmg, _, hinj⟩ := exists_distinct_critical_values hf hm
  exact ⟨g, hg, hmg, finite_criticalPoints hg hmg, hinj⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
