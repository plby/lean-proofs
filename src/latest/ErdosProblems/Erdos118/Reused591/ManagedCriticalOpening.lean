import ErdosProblems.Erdos118.Reused591.ManagedHandoff
import ErdosProblems.Erdos118.Reused591.NextMarkerReplayHistory

namespace Erdos118.Reused591

/-!
# A managed opposite leaf followed by the pending first-word continuation

This common opening is shared by the singleton and late-marker inside
cases. It makes no assumption about terminal body sizes or marker order.
The first word remains unchanged and its next size-zero reply is pending.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem managed_critical_opening {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hrel : p.position.board.left.relaxed = true)
    (hsep : ∀ y ∈ p.position.board.right.coordinates,
      y ≤ p.position.board.left.coordinates.getLastD 0)
    {i : ℕ} (hi : LabeledWord.BeforeBody i p.position.board.left)
    {t mode : Bool} {other : LabeledWord} (upperOrigin : Concrete.Hist N)
    (hmanaged : ∃ M : Managed N H blue b σ t mode other p.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧
      q.position.board.left = p.position.board.left ∧ q.position.board.right.relaxed = true ∧
      (∀ y ∈ q.position.board.left.coordinates,
        y ≤ q.position.board.right.coordinates.getLastD 0) ∧
      ∃ M : Managed N H blue b σ t mode other q.position.board.right,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target := by
  obtain ⟨v, hpv, hvn, hvr, hvo, hvsep, Mv, hMv⟩ :=
    managed_next_opposite_leaf_from hHN hH blue hwin false hrel hsep
      (Or.inl ⟨i, hi⟩) upperOrigin hmanaged
  change v.position.board.right.relaxed = true at hvr
  change ∀ y ∈ v.position.board.left.coordinates,
    y ≤ v.position.board.right.coordinates.getLastD 0 at hvsep
  have hvo' : v.position.board.left = p.position.board.left := hvo
  have hvbefore : LabeledWord.BeforeBody i v.position.board.left := by
    simpa only [hvo'] using hi
  have hvlive := hvbefore.not_terminal ((Position.history_dataInvariant v).2.1 false).1
  obtain ⟨q, r, hvq, hboard, hp⟩ :=
    request_on_live_board σ v (Board.not_done_of_live (side := false) hvlive)
  have hpq := hpv.trans hvq
  have hwinq := hwin.of_reachable (exactGame N blue) hpq
  have hside : r.side = false := winning_pending_switch hHN hH blue hwinq hp true
    (by simpa [hboard, Board.get] using hvr) (by simpa [hboard, Board.get] using hvsep)
  have hleft : q.position.board.left = p.position.board.left := by
    simpa only [hboard] using hvo'
  have hzero := winning_pending_root_advance_zero hHN hH blue hwinq hp false hside
    (by simpa only [Board.get, hleft] using hrel)
    (by simpa only [Board.get, hleft] using hi)
  have hpzero : q.position.pending = some ⟨false, .advance 0⟩ := by
    simpa only [hzero] using hp
  refine ⟨q, hpq, hpzero, hleft, by simpa only [hboard, Board.get] using hvr,
    by simpa only [hboard, Board.get] using hvsep, ?_⟩
  rw [hboard]
  exact ⟨Mv, hMv⟩

#print axioms managed_critical_opening

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
