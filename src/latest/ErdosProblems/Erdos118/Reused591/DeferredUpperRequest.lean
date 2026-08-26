import ErdosProblems.Erdos118.Reused591.ManagedDeferred
import ErdosProblems.Erdos118.Reused591.PendingNextLeaf

namespace Erdos118.Reused591

/-!
# Fire the inserted opposite leaf and fix the upper next-leaf request

After the deferred right-word response, the unchanged left word still
has its specified next selected leaf. The upper strategy therefore
requests that continuation. Its actual bound is now fixed, while all
candidate-label and literal-prefix data remain available.
-/

namespace Erdos591.Positive.Game.Relay.Managed

open Erdos591.Negative.Exact
open Payoff

theorem fire_deferred_then_other_next {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {other w : LabeledWord} (M : Managed N H blue b σ true true other w)
    (hinc : w.coordinates.Pairwise (· < ·)) (hrel : w.relaxed = true)
    (hlastBody : w.lastSelectedBody = w.bodyLabels.length)
    (hlater : ∃ k ∈ w.currentLabel, w.leafIndex < k)
    {j : ℕ} (htarget : LabeledWord.UpToLeaf j other) (hstrict : other.leafIndex < j)
    (origin : Concrete.Hist N)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q ∧
      (exactGame N blue).ArchitectWins H b σ q ∧ q.position.mode = some true ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧ q.position.board.left = other ∧
      q.position.board.right.coordinates = w.coordinates ∧ q.position.board.right.relaxed = true ∧
      q.position.board.right.leafIndex = w.leafIndex ∧
      (q.position.board.right.currentLabel.card = 1 →
        q.position.board.right.currentLabel = {w.leafIndex}) ∧
      (2 ≤ q.position.board.right.currentLabel.card →
        w.currentLabel.sup id ∈ q.position.board.right.currentLabel ∧
        ∀ k ∈ q.position.board.right.currentLabel,
          w.leafIndex < k → w.currentLabel.sup id ≤ k) := by
  obtain ⟨v, hov, hwinv, _hvn, hvc, hvr, hvi, hvo, hvm, hvsep, hsingle, hsecond,
      _hcard, _hfirst⟩ :=
    M.fire_deferred_from hHN hinc hrel hlastBody hlater origin hfrom
  have hleft : v.position.board.left = other := hvo
  obtain ⟨q, hvq, hboard, hp⟩ := winning_next_leaf_request_after_other hHN hH blue hwinv false
    (by simpa [Board.get, hleft] using htarget)
    (by simpa [Board.get, hleft] using hstrict) hvr hvsep
  exact ⟨q, hov.trans hvq, hwinv.of_reachable (exactGame N blue) hvq,
    follow_mode_some hvq hvm, hp, by simpa [hboard] using hleft,
    by simpa [hboard, Board.get] using hvc, by simpa [hboard, Board.get] using hvr,
    by simpa [hboard, Board.get] using hvi, by simpa [hboard, Board.get] using hsingle,
    by simpa [hboard, Board.get] using hsecond⟩

#print axioms fire_deferred_then_other_next

end Erdos591.Positive.Game.Relay.Managed

end Erdos118.Reused591
