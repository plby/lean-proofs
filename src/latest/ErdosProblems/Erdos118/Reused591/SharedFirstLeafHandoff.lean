import ErdosProblems.Erdos118.Reused591.FirstLeafGluingHistory
import ErdosProblems.Erdos118.Reused591.FreshLeafNextMarker
import ErdosProblems.Erdos118.Reused591.PendingNextLeaf

namespace Erdos118.Reused591

/-!
# Shared first leaf with different next events in the two plays

The common word is the lower play's second word and either upper word.
After the same first selected leaf, the lower play requests
an unread leaf of its other word, while the upper play requests its
other word's next selection, in the current or a future body.
Both actual bounds are now available.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem shared_first_leaf_handoff {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (lower upper : Concrete.Hist N) (t : Bool)
    {B p q j : ℕ} (L : LastFirstLabels H B 1 p) (U : LastFirstLabels H B 1 q)
    (hfirst : U.pivot = L.pivot) (hmarker : U.marker = L.marker)
    (hwinL : (exactGame N blue).ArchitectWins H b σ lower)
    (hwinU : (exactGame N blue).ArchitectWins H b σ upper)
    (hpL : lower.position.pending = some ⟨true, .advance p⟩)
    (hpU : upper.position.pending = some ⟨t, .advance q⟩)
    (hmL : lower.position.board.right.markerEvent = true)
    (hmU : (upper.position.board.get t).markerEvent = true)
    (hsame : LabeledWord.SameStructure lower.position.board.right (upper.position.board.get t))
    (hS : LabeledWord.UpToLeaf j lower.position.board.left)
    (hSstrict : lower.position.board.left.leafIndex < j)
    (hUrel : (upper.position.board.get (!t)).relaxed = true)
    (hUpending : Macro.Pending (upper.position.board.get (!t)))
    (hBL : max lower.position.bound (b lower) ≤ B)
    (hBU : max upper.position.bound (b upper) ≤ B) :
    ∃ v w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) lower v ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upper w ∧
      v.position.pending = some ⟨false, .advance 0⟩ ∧
      w.position.pending = some ⟨!t, .advance 0⟩ ∧
      LabeledWord.SameStructure v.position.board.right (w.position.board.get t) ∧
      v.position.board.right.relaxed = true ∧ (w.position.board.get t).relaxed = true ∧
      v.position.board.right.currentLabel = L.upper ∧
      (w.position.board.get t).currentLabel = U.upper ∧
      v.position.board.right.leafIndex = L.pivot ∧ (w.position.board.get t).leafIndex = L.pivot ∧
      v.position.board.right.bodyLabels = lower.position.board.right.bodyLabels ++ [L.upper] ∧
      (w.position.board.get t).bodyLabels = (upper.position.board.get t).bodyLabels ++ [U.upper] ∧
      v.position.board.right.rootLabel = lower.position.board.right.rootLabel ∧
      (w.position.board.get t).rootLabel = (upper.position.board.get t).rootLabel ∧
      v.position.board.left = lower.position.board.left ∧
      w.position.board.get (!t) = upper.position.board.get (!t) := by
  obtain ⟨v₀, w₀, hLv, hUw, _hnv, _hnw, hshape, hrelV, hrelW, hiV, hiW,
      hbodyV, hbodyW, hotherV, hotherW, r, xs, _hparse, hwordV, hwordW,
      _hlen, _hinc, _hpool⟩ := first_leaf_gluing_prefix hHN hH blue σ lower upper true t L U
    hfirst hmarker hpL hpU hmL hmU hsame hBL hBU
  have hsepV := (FiniteResponseGame.FollowStep.next (exactGame N blue) hLv).reply_separation hpL
  have hsepW := (FiniteResponseGame.FollowStep.next (exactGame N blue) hUw).reply_separation hpU
  change v₀.position.board.left = lower.position.board.left at hotherV
  obtain ⟨v, hv₀v, hvBoard, hpv⟩ := winning_next_leaf_request_after_other hHN hH blue
    (hwinL.of_reachable (exactGame N blue) (.single hLv)) false
    (by change LabeledWord.UpToLeaf j v₀.position.board.left; rw [hotherV]; exact hS)
    (by change v₀.position.board.left.leafIndex < j; rw [hotherV]; exact hSstrict)
    hrelV hsepV
  obtain ⟨w, hw₀w, hwBoard, hpw⟩ := winning_next_selection_after_fresh_leaf hHN hH blue
    (hwinU.of_reachable (exactGame N blue) (.single hUw)) t hrelW hsepW
    (by rw [hotherW]; exact hUrel) (by rw [hotherW]; exact hUpending)
  change LabeledWord.SameStructure v₀.position.board.right (w₀.position.board.get t) at hshape
  change v₀.position.board.right.relaxed = true at hrelV
  change v₀.position.board.right.leafIndex = L.pivot at hiV
  change v₀.position.board.right.bodyLabels = lower.position.board.right.bodyLabels ++ [L.upper]
    at hbodyV
  change v₀.position.board.right =
    LabeledWord.bodyLeafCursor lower.position.board.right L.upper L.marker r xs at hwordV
  refine ⟨v, w, (Relation.ReflTransGen.single hLv).trans hv₀v,
    (Relation.ReflTransGen.single hUw).trans hw₀w, hpv, hpw, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hvBoard, hwBoard] using hshape
  · simpa only [hvBoard] using hrelV
  · simpa only [hwBoard] using hrelW
  · simp [hvBoard, LabeledWord.currentLabel, hbodyV]
  · simp [hwBoard, LabeledWord.currentLabel, hbodyW]
  · simpa only [hvBoard] using hiV
  · simpa only [hwBoard] using hiW
  · simpa only [hvBoard] using hbodyV
  · simpa only [hwBoard] using hbodyW
  · simp [hvBoard, hwordV, LabeledWord.bodyLeafCursor]
  · simp [hwBoard, hwordW, LabeledWord.bodyLeafCursor]
  · simpa only [hvBoard] using hotherV
  · simpa only [hwBoard] using hotherW

#print axioms shared_first_leaf_handoff

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
