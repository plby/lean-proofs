import Wikipedia.HopfProblem.DegreeCollapseConnectedMinimumCancellation
import Wikipedia.HopfProblem.DegreeCollapseDualMorsePairRemoval
import Wikipedia.HopfProblem.DegreeCollapseMinimalOrderedMorse

/-!
# A count-minimal excellent Morse function has unique extrema

On a compact connected native manifold, the constructed zero/one cancellation
contradicts count minimality whenever the minimum count differs from one.
Negating the function gives the corresponding assertion for maxima. In
particular the existing globally ordered, count-minimal system now has
exactly one point at each extreme index. Intermediate indices are not
eliminated here, and the total critical count is not asserted to be two.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}

theorem minimal_excellent_morse_minimum_count_one
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hminimal : ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
      InjOn g (criticalPoints E g) →
      (criticalPoints E f).ncard ≤ (criticalPoints E g).ncard) :
    nativeMorseCount E f 0 = 1 := by
  by_contra hmin
  obtain ⟨g, hg, hmg, hinjg, hcount⟩ :=
    exists_excellent_morse_reduction_of_multiple_minima S hf hm hmin
  exact minimal_excellent_morse_forbids_pair_removal hminimal hg hmg hinjg hcount

theorem minimal_excellent_morse_extreme_counts_one
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hminimal : ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
      InjOn g (criticalPoints E g) →
      (criticalPoints E f).ncard ≤ (criticalPoints E g).ncard) :
    nativeMorseCount E f 0 = 1 ∧ nativeMorseCount E f (Module.finrank ℝ E) = 1 := by
  refine ⟨minimal_excellent_morse_minimum_count_one S hf hm hminimal, ?_⟩
  obtain ⟨T⟩ := nonempty_adaptedSurgeryWindows hf.neg (isMorse_neg hm)
    (distinct_critical_values_neg S.distinct)
  have hmin := minimal_excellent_morse_minimum_count_one T hf.neg (isMorse_neg hm)
    (minimal_excellent_morse_neg hminimal)
  have hcounts := nativeMorseCount_neg hf hm (le_refl (Module.finrank ℝ E))
  rw [Nat.sub_self] at hcounts
  exact hcounts.symm.trans hmin

variable (E M) in
theorem exists_minimal_ordered_morse_system_with_unique_extrema :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      ∃ S : AdaptedSurgeryWindows E f,
        (∀ p q : criticalPoints E f, f p < f q →
          nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
        nativeMorseCount E f 0 = 1 ∧ nativeMorseCount E f (Module.finrank ℝ E) = 1 ∧
        ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
          InjOn g (criticalPoints E g) →
          (criticalPoints E f).ncard ≤ (criticalPoints E g).ncard := by
  obtain ⟨f, hf, hm, S, horder, hminimal⟩ :=
    exists_minimal_index_ordered_excellent_morse_system E M
  obtain ⟨hmin, hmax⟩ := minimal_excellent_morse_extreme_counts_one S hf hm hminimal
  exact ⟨f, hf, hm, S, horder, hmin, hmax, hminimal⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
