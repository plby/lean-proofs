import ErdosProblems.Erdos118.Reused591.DelayedFirstLeaf
import ErdosProblems.Erdos118.Reused591.LastLastUpper

namespace Erdos118.Reused591

/-!
# Enter the second middle phase after the first phase's retained prefix

All lower nonlast leaf coordinates are already fixed, but lie strictly
before the upper first selected leaf. Extend only the missing suffix
above the new bounds, submit the delayed upper body response, and retain
the exact virtual-prefix continuation for the lower final-leaf replay.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_second_middle_start {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    (σ : (exactGame N blue).ArchitectStrategy) (p : Concrete.Hist N)
    {B a c : ℕ} (L : LastLastLabels H B a c)
    (hp : p.position.pending = some ⟨false, .advance c⟩)
    (hm : p.position.board.left.markerEvent = true) {r : ℕ}
    (hparse : p.position.board.left.parser = .blocks (r + 1))
    (hroot : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1)
    (hB : max p.position.bound (b p) ≤ B) (xs : List ℕ)
    (hlen : xs.length = L.penultimate) (hinc : (L.marker :: xs).Pairwise (· < ·))
    (hpool : ∀ x ∈ xs, x ∈ H) (C : ℕ) :
    ∃ q ys, (exactGame N blue).FollowStep σ H b p q ∧ q.position.pending = none ∧
      q.position.board.left.relaxed = true ∧
      LabeledWord.UpToLeaf L.upperPenultimate q.position.board.left ∧
      L.pivot ∈ q.position.board.left.currentLabel ∧
      (∀ i ∈ q.position.board.left.currentLabel, i = L.pivot ∨ i ≤ L.upperPenultimate) ∧
      (∀ i ∈ q.position.board.left.rootLabel, i ≤ q.position.board.left.bodyLabels.length) ∧
      q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ++ [L.upper] ∧
      q.position.board.left.bodyMarker = L.marker ∧
      q.position.board.right = p.position.board.right ∧
      (∀ y ∈ q.position.board.right.coordinates,
        y ≤ q.position.board.left.coordinates.getLastD 0) ∧ C < q.position.bound ∧
      q.position.board.left =
        LabeledWord.bodyLeafCursor p.position.board.left L.upper L.marker r (xs ++ ys) ∧
      (xs ++ ys).length = L.firstUpper ∧ (L.marker :: (xs ++ ys)).Pairwise (· < ·) ∧
      (∀ y ∈ ys, y ∈ H ∧ C < y) ∧
      LabeledWord.LegalRun (LabeledWord.bodyLeafCursor p.position.board.left L.upper L.marker r xs)
        (ys.map fun y => (∅, y)) q.position.board.left := by
  obtain ⟨q, ys, hstep, hn, hr, hword, hfullLen, hfullInc, hys, hbound, hrun, hother, hsep⟩ :=
    delayed_first_leaf_from_prefix hHN hH blue σ p false L.first_to_upper hp hm hparse hB xs
      (by simpa only [LastLastLabels.first_to_upper, hlen] using L.penultimate_lt_firstUpper)
      hinc hpool C
  change q.position.board.left =
    LabeledWord.bodyLeafCursor p.position.board.left L.upper L.marker r (xs ++ ys) at hword
  change q.position.board.left.relaxed = true at hr
  change (xs ++ ys).length = L.firstUpper at hfullLen
  have hcurrent : q.position.board.left.currentLabel = L.upper := by
    simp [hword, LabeledWord.bodyLeafCursor, LabeledWord.currentLabel]
  have htarget : LabeledWord.UpToLeaf L.upperPenultimate q.position.board.left :=
    ⟨(of_decide_eq_true hr).2.1, hcurrent ▸ L.upperPenultimate_mem,
      by simpa [hword, LabeledWord.bodyLeafCursor, hfullLen] using L.firstUpper_le_upperPenultimate⟩
  exact ⟨q, ys, hstep, hn, hr, htarget, hcurrent ▸ L.pivot_upper,
    by simpa only [hcurrent] using L.upper_bounds_penultimate,
    by simpa [hword, LabeledWord.bodyLeafCursor] using hroot,
    by simp [hword, LabeledWord.bodyLeafCursor], by simp [hword, LabeledWord.bodyLeafCursor],
    hother, hsep, hbound, hword, hfullLen, hfullInc, hys, hrun⟩

#print axioms inside_second_middle_start

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
