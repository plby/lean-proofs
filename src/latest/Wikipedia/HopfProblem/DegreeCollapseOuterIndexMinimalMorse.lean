import Wikipedia.HopfProblem.DegreeCollapseMinimalMinimumCount
import Wikipedia.HopfProblem.DegreeCollapseOrderedMiddleCut

/-!
# Minimize the outer intermediate indices at fixed minimal total count

The natural-valued cost is the sum of the intrinsic index-one and index-five
counts. Its minimum among total-count-minimal excellent Morse functions
exists by well-ordering. Actual native index ordering preserves every count,
so it also preserves both minimizations. The extrema are already unique.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M]

variable (E M) in
theorem exists_outer_index_minimal_ordered_morse_system :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      ∃ S : AdaptedSurgeryWindows E f,
        (∀ p q : criticalPoints E f, f p < f q →
          nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
        nativeMorseCount E f 0 = 1 ∧ nativeMorseCount E f (Module.finrank ℝ E) = 1 ∧
        (∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
          InjOn g (criticalPoints E g) →
          (criticalPoints E f).ncard ≤ (criticalPoints E g).ncard) ∧
        ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
          InjOn g (criticalPoints E g) →
          (criticalPoints E g).ncard = (criticalPoints E f).ncard →
          nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
            nativeMorseCount E g 1 + nativeMorseCount E g 5 := by
  classical
  obtain ⟨f₀, hf₀, hm₀, S₀, hminimal₀⟩ := exists_minimal_excellent_morse_system E M
  let P : ℕ → Prop := fun n => ∃ f : M → ℝ,
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧ InjOn f (criticalPoints E f) ∧
    (criticalPoints E f).ncard = (criticalPoints E f₀).ncard ∧
    nativeMorseCount E f 1 + nativeMorseCount E f 5 = n
  have hex : ∃ n, P n := ⟨_, f₀, hf₀, hm₀, S₀.distinct, rfl, rfl⟩
  obtain ⟨g, hg, hmg, hinjg, hcardg, hcostg⟩ := Nat.find_spec hex
  obtain ⟨T⟩ := nonempty_adaptedSurgeryWindows hg hmg hinjg
  obtain ⟨f, hf, hm, hcrit, -, S, horder, hcounts⟩ :=
    exists_index_ordered_morse_system_preserving_critical_points T hg hmg
  have hcardf : (criticalPoints E f).ncard = (criticalPoints E f₀).ncard := by
    rw [hcrit, hcardg]
  have hminimal : ∀ h : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h → IsMorse E h →
      InjOn h (criticalPoints E h) →
      (criticalPoints E f).ncard ≤ (criticalPoints E h).ncard := by
    intro h hh hmh hinjh
    rw [hcardf]
    exact hminimal₀ h hh hmh hinjh
  obtain ⟨hmin, hmax⟩ := minimal_excellent_morse_extreme_counts_one S hf hm hminimal
  refine ⟨f, hf, hm, S, horder, hmin, hmax, hminimal, ?_⟩
  intro h hh hmh hinjh hcardh
  rw [hcounts 1, hcounts 5, hcostg]
  exact Nat.find_min' hex ⟨h, hh, hmh, hinjh, hcardh.trans hcardf, rfl⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
