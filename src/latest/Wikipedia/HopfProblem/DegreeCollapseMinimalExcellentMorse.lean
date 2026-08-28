import Wikipedia.HopfProblem.DegreeCollapseAdaptedSurgeryWindows

/-!
# An actual excellent Morse function with least critical-point count

The already constructed excellent functions form a nonempty class. The
well-ordering of their actual finite critical counts selects a least one,
and the common-flow construction supplies its original native surgeries.
This provides a global minimization formulation of the remaining handle
selection problem; it does not assert that the minimum count is two.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

variable (E M) in
theorem exists_minimal_excellent_morse_system :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      ∃ S : AdaptedSurgeryWindows E f,
        ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
          InjOn g (criticalPoints E g) →
          (criticalPoints E f).ncard ≤ (criticalPoints E g).ncard := by
  classical
  let P : ℕ → Prop := fun n => ∃ f : M → ℝ,
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      InjOn f (criticalPoints E f) ∧ (criticalPoints E f).ncard = n
  obtain ⟨f₀, hf₀, hm₀, -, hinj₀⟩ := exists_morse_function_with_distinct_critical_values E M
  have hex : ∃ n, P n := ⟨(criticalPoints E f₀).ncard, f₀, hf₀, hm₀, hinj₀, rfl⟩
  obtain ⟨f, hf, hm, hinj, hcard⟩ := Nat.find_spec hex
  obtain ⟨S⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  refine ⟨f, hf, hm, S, ?_⟩
  intro g hg hmg hinjg
  rw [hcard]
  exact Nat.find_min' hex ⟨g, hg, hmg, hinjg, rfl⟩

theorem minimal_excellent_morse_forbids_pair_removal {f g : M → ℝ}
    (hminimal : ∀ h : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h → IsMorse E h →
      InjOn h (criticalPoints E h) →
      (criticalPoints E f).ncard ≤ (criticalPoints E h).ncard)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : IsMorse E g)
    (hinjg : InjOn g (criticalPoints E g)) :
    (criticalPoints E g).ncard + 2 ≠ (criticalPoints E f).ncard := by
  have hle := hminimal g hg hmg hinjg
  omega

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
