import Wikipedia.HopfProblem.DegreeCollapseOrderedNativeMorseSystem
import Wikipedia.HopfProblem.DegreeCollapseMinimalExcellentMorse

/-!
# An actual excellent Morse system that is both ordered and count-minimal

Start with the constructed excellent Morse function of least critical
count. Global native index ordering preserves its entire critical set,
so it retains count minimality. This combines the geometric ordering
theorem with the finite minimization needed for later handle elimination;
it does not assert that the minimum count is two.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

variable (E M) in
theorem exists_minimal_index_ordered_excellent_morse_system :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      ∃ S : AdaptedSurgeryWindows E f,
        (∀ p q : criticalPoints E f, f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
        ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
          InjOn g (criticalPoints E g) → (criticalPoints E f).ncard ≤ (criticalPoints E g).ncard := by
  obtain ⟨f₀, hf₀, hm₀, S₀, hminimal⟩ := exists_minimal_excellent_morse_system E M
  obtain ⟨f, hf, hm, hcrit, -, S, horder, -⟩ :=
    exists_index_ordered_morse_system_preserving_critical_points S₀ hf₀ hm₀
  refine ⟨f, hf, hm, S, horder, ?_⟩
  intro g hg hmg hinj
  rw [hcrit]
  exact hminimal g hg hmg hinj

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
