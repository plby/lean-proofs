import Wikipedia.HopfProblem.DegreeCollapseRelativeCriticalValue

/-!
# Distinct critical values with exact support and uniform value control

Finite induction separates the original native critical values while
preserving every critical point and fixing the function outside the
allowed open region. Splitting the requested positive error between the
previous approximation and the next local perturbation keeps a uniform
bound on the actual function throughout the construction.
-/

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularTimeMorse

open Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_distinct_critical_values_relative {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (O : Set M) (hO : IsOpen O) (hKO : criticalPoints E f ⊆ O) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      criticalPoints E g = criticalPoints E f ∧ InjOn g (criticalPoints E g) ∧
      (∀ x : M, |g x - f x| < ε) ∧ EqOn g f Oᶜ := by
  classical
  let K := criticalPoints E f
  have hK : K.Finite := finite_criticalPoints hf hm
  have hfinite : ∀ s : Finset M, (s : Set M) ⊆ K → ∀ η : ℝ, 0 < η →
      ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
        criticalPoints E g = K ∧ InjOn g (s : Set M) ∧
        (∀ x : M, |g x - f x| < η) ∧ EqOn g f Oᶜ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ η hη
      exact ⟨f, hf, hm, rfl, by simp, fun x ↦ by simpa using hη, fun _ _ ↦ rfl⟩
    | @insert p s hps ih =>
      intro hsK η hη
      have hsK' : (s : Set M) ⊆ K := fun x hx ↦ hsK (Finset.mem_insert_of_mem hx)
      obtain ⟨g, hg, hmg, hcrit, hinj, hclose, hfixed⟩ := ih hsK' (η / 2) (half_pos hη)
      have hpO : p ∈ O := hKO (hsK (Finset.mem_insert_self p s))
      obtain ⟨g', hg', hmg', hcrit', hvalues, hunique, hclose', hfixed'⟩ :=
        exists_separating_critical_value_relative hg hmg O hO p hpO (η / 2) (half_pos hη)
      have hK' : criticalPoints E g' = K := hcrit'.trans hcrit
      refine ⟨g', hg', hmg', hK', ?_, ?_, ?_⟩
      · intro x hx y hy heq
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
        rw [← hvalues x hxcrit hxp, ← hvalues y hycrit hyp]
        exact heq
      · intro x
        calc
          |g' x - f x| = |(g' x - g x) + (g x - f x)| := by congr 1; ring
          _ ≤ |g' x - g x| + |g x - f x| := by
            simpa only [Real.norm_eq_abs] using norm_add_le (g' x - g x) (g x - f x)
          _ < η / 2 + η / 2 := add_lt_add (hclose' x) (hclose x)
          _ = η := by ring
      · intro x hx
        exact (hfixed' hx).trans (hfixed hx)
  obtain ⟨g, hg, hmg, hcrit, hinj, hclose, hfixed⟩ := hfinite hK.toFinset (by simp) ε hε
  refine ⟨g, hg, hmg, hcrit, ?_, hclose, hfixed⟩
  rw [hcrit]
  simpa only [hK.coe_toFinset] using hinj

end Wikipedia.HopfProblem.DegreeCollapse.RegularTimeMorse
