import ErdosProblems.Erdos118.Reused591.NextLeafReplayHistory
import ErdosProblems.Erdos118.Reused591.BoundaryRequests

namespace Erdos118.Reused591

/-!
# The pending next-leaf request after a fresh opposite selected leaf

A fresh opposite selected leaf forces a switch to the specified word.
Its fixed unread selected leaf then forces a size-zero advance. The
actual pending history exposes its bound before any new coordinate is
created for the delayed replay.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_next_leaf_request_after_other {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) {j : ℕ} (htarget : LabeledWord.UpToLeaf j (p.position.board.get side))
    (hstrict : (p.position.board.get side).leafIndex < j)
    (hother : (p.position.board.get (!side)).relaxed = true)
    (hsep : ∀ y ∈ (p.position.board.get side).coordinates,
      y ≤ (p.position.board.get (!side)).coordinates.getLastD 0) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.board = p.position.board ∧
      q.position.pending = some ⟨side, .advance 0⟩ := by
  obtain ⟨r, k, hparse⟩ := htarget.parser_leaves ((Position.history_dataInvariant p).2.1 side).1
  have hlive : (p.position.board.get side).terminal = false := by
    simp [LabeledWord.terminal, hparse]
  obtain ⟨q, req, hpath, hboard, hp⟩ := request_on_live_board σ p (Board.not_done_of_live hlive)
  have hwinq := hwin.of_reachable (exactGame N blue) hpath
  have hside : req.side = side := by
    simpa using winning_pending_switch hHN hH blue hwinq hp (!side)
      (by simpa only [hboard] using hother) (by simpa only [hboard, Bool.not_not] using hsep)
  have hreq := winning_pending_leaf_advance_zero hHN hH blue hwinq hp side hside
    (by simpa only [hboard] using htarget) (by simpa only [hboard] using hstrict)
  exact ⟨q, hpath, hboard, by simpa only [hreq] using hp⟩

#print axioms winning_next_leaf_request_after_other

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
