import Wikipedia.HopfProblem.DegreeCollapsePositiveZeroOneCancellation

/-!
# Secondary Morse minimality with the original zero boundary fixed

A one-to-three handle trade preserves the total number of critical points.
Minimize a second natural-valued cost among excellent presentations with
minimal total count, then apply the actual positive ordering theorem. Every
indexed count is preserved by that ordering. In dimension seven the outer
interior cost counts indices one and six. Positive births are still excluded
by the already constructed native zero/one cancellation.

This is a minimization theorem, not an existence assertion for the required
relative handle trades.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open MorseCancellation

variable {B : Type} [TopologicalSpace B]

theorem exists_count_cost_minimal_positive_ordered_presentation
    (S : CollaredSevenState B) (cost : (ℕ → ℕ) → ℕ) :
    ∃ P : S.ExcellentMorsePresentation,
      (∀ p q : criticalPoints (Vector 7) P.function,
        0 < P.function p → P.function p < P.function q →
          nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q) ∧
      (∀ Q : S.ExcellentMorsePresentation,
        (criticalPoints (Vector 7) P.function).ncard ≤
          (criticalPoints (Vector 7) Q.function).ncard) ∧
      ∀ Q : S.ExcellentMorsePresentation,
        (criticalPoints (Vector 7) Q.function).ncard =
          (criticalPoints (Vector 7) P.function).ncard →
        cost (nativeMorseCount (Vector 7) P.function) ≤
          cost (nativeMorseCount (Vector 7) Q.function) := by
  classical
  obtain ⟨P₀, _, hminimal₀⟩ := S.exists_minimal_positive_index_ordered_presentation
  let C : ℕ → Prop := fun n => ∃ Q : S.ExcellentMorsePresentation,
    (criticalPoints (Vector 7) Q.function).ncard =
      (criticalPoints (Vector 7) P₀.function).ncard ∧
    cost (nativeMorseCount (Vector 7) Q.function) = n
  have hex : ∃ n, C n := ⟨_, P₀, rfl, rfl⟩
  obtain ⟨Q, hcardQ, hcostQ⟩ := Nat.find_spec hex
  obtain ⟨P, hcrit, _, _, horder, hcounts⟩ := Q.exists_positive_index_ordered
  have hcardP : (criticalPoints (Vector 7) P.function).ncard =
      (criticalPoints (Vector 7) P₀.function).ncard := by
    rw [hcrit, hcardQ]
  refine ⟨P, horder, ?_, ?_⟩
  · intro R
    rw [hcardP]
    exact hminimal₀ R
  · intro R hcardR
    rw [funext hcounts, hcostQ]
    exact Nat.find_min' hex ⟨R, hcardR.trans hcardP, rfl⟩

theorem exists_outer_index_minimal_positive_ordered_presentation
    (S : CollaredSevenState B) (eBoundary : B ≃ₜ Sphere 6) :
    ∃ P : S.ExcellentMorsePresentation,
      (∀ p q : criticalPoints (Vector 7) P.function,
        0 < P.function p → P.function p < P.function q →
          nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q) ∧
      (∀ Q : S.ExcellentMorsePresentation,
        (criticalPoints (Vector 7) P.function).ncard ≤
          (criticalPoints (Vector 7) Q.function).ncard) ∧
      (∀ Q : S.ExcellentMorsePresentation,
        (criticalPoints (Vector 7) Q.function).ncard =
          (criticalPoints (Vector 7) P.function).ncard →
        nativeMorseCount (Vector 7) P.function 1 + nativeMorseCount (Vector 7) P.function 6 ≤
          nativeMorseCount (Vector 7) Q.function 1 + nativeMorseCount (Vector 7) Q.function 6) ∧
      ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
        nativeMorseIndex (Vector 7) P.function p ≠ 0 := by
  obtain ⟨P, horder, hminimal, hcost⟩ :=
    S.exists_count_cost_minimal_positive_ordered_presentation (fun c => c 1 + c 6)
  exact ⟨P, horder, hminimal, hcost, P.no_positive_index_zero_of_minimal eBoundary hminimal⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
