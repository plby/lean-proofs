import Wikipedia.HopfProblem.DegreeCollapsePositiveOneThreeTrade

/-!
# Eliminate every positive index-one critical point in the original state

The actual supported one-to-three trade preserves total critical count,
reduces index-one count by one, and preserves index-six count. It therefore
contradicts the secondary outer-index minimum. Together with the already
constructed positive birth elimination and native ordering, this gives an
excellent presentation of the SAME state whose every positive critical
point has index at least two. The original zero boundary and atlases remain.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}

namespace ExcellentMorsePresentation

theorem no_positive_index_one_of_outer_minimal [PathConnectedSpace B]
    (P : S.ExcellentMorsePresentation)
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (hnobirth : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      nativeMorseIndex (Vector 7) P.function p ≠ 0)
    (hcost : ∀ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) Q.function).ncard =
        (criticalPoints (Vector 7) P.function).ncard →
      nativeMorseCount (Vector 7) P.function 1 + nativeMorseCount (Vector 7) P.function 6 ≤
        nativeMorseCount (Vector 7) Q.function 1 + nativeMorseCount (Vector 7) Q.function 6)
    (q : criticalPoints (Vector 7) P.function) (hq : 0 < P.function q) :
    nativeMorseIndex (Vector 7) P.function q ≠ 1 := by
  intro hqone
  obtain ⟨Q, hcard, hone, _, hother, _⟩ :=
    P.exists_positive_one_to_three_handle_trade horder hnobirth q hq hqone
  have hminimal := hcost Q hcard
  have hsix := hother 6 (by decide) (by decide)
  omega

end ExcellentMorsePresentation

theorem exists_minimal_positive_ordered_presentation_without_low_indices
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
        2 ≤ nativeMorseIndex (Vector 7) P.function p := by
  let : PathConnectedSpace B := pathConnectedSpace_of_homotopyEquiv eBoundary.toHomotopyEquiv
  obtain ⟨P, horder, hminimal, hcost, hnobirth⟩ :=
    S.exists_outer_index_minimal_positive_ordered_presentation eBoundary
  refine ⟨P, horder, hminimal, hcost, ?_⟩
  intro p hp
  have hzero := hnobirth p hp
  have hone := P.no_positive_index_one_of_outer_minimal horder hnobirth hcost p hp
  omega

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
