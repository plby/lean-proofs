import ErdosProblems.Erdos591.InsideLastLeafBoundary
import ErdosProblems.Erdos591.NextLeafReplayHistory

/-!
# The managed opposite endpoint before the common final leaf

From the penultimate first-word selected leaf, take the next managed
opposite selected leaf and leave the first word's final-leaf response
pending. The test boundary identifies the opposite leaf as its last.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_last_leaf_checkpoint {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some true)
    (hrel : p.position.board.left.relaxed = true)
    (hsep : ∀ y ∈ p.position.board.right.coordinates,
      y ≤ p.position.board.left.coordinates.getLastD 0)
    {j : ℕ} (htarget : LabeledWord.UpToLeaf j p.position.board.left)
    (hstrict : p.position.board.left.leafIndex < j)
    (hnext : ∀ k ∈ p.position.board.left.currentLabel,
      p.position.board.left.leafIndex < k → j ≤ k)
    (hrootLast : ∀ k ∈ p.position.board.left.rootLabel,
      k ≤ p.position.board.left.bodyLabels.length)
    (hleafLast : ∀ k ∈ p.position.board.left.currentLabel, k ≤ j)
    {t mode : Bool} {other : LabeledWord} (upperOrigin : Concrete.Hist N)
    (hmanaged : ∃ M : Managed N H blue b σ t mode other p.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧
      q.position.board.left = p.position.board.left ∧ q.position.board.right.relaxed = true ∧
      (∀ y ∈ q.position.board.left.coordinates,
        y ≤ q.position.board.right.coordinates.getLastD 0) ∧
      ¬ Macro.Pending q.position.board.right ∧
      ∃ M : Managed N H blue b σ t mode other q.position.board.right,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target := by
  obtain ⟨v, hpv, hvn, hvr, hvo, hvsep, Mv, hMv⟩ :=
    managed_next_opposite_leaf_from hHN hH blue hwin false hrel hsep
      (Or.inr ⟨htarget.selected, j, htarget.mem, hstrict⟩) upperOrigin hmanaged
  change v.position.board.right.relaxed = true at hvr
  change ∀ y ∈ v.position.board.left.coordinates,
    y ≤ v.position.board.right.coordinates.getLastD 0 at hvsep
  have hvo' : v.position.board.left = p.position.board.left := hvo
  have hvtarget : LabeledWord.UpToLeaf j v.position.board.left := by
    simpa only [hvo'] using htarget
  obtain ⟨r, k, hvparse⟩ := hvtarget.parser_leaves ((Position.history_dataInvariant v).2.1 false).1
  have hvlive : v.position.board.left.terminal = false := by
    simp [LabeledWord.terminal, hvparse]
  obtain ⟨q, req, hvq, hboard, hp⟩ :=
    request_on_live_board σ v (Board.not_done_of_live (side := false) hvlive)
  have hpq := hpv.trans hvq
  have hwinq := hwin.of_reachable (exactGame N blue) hpq
  have hside : req.side = false := winning_pending_switch hHN hH blue hwinq hp true
    (by simpa [hboard, Board.get] using hvr) (by simpa [hboard, Board.get] using hvsep)
  have hleft : q.position.board.left = p.position.board.left := by
    simpa only [hboard] using hvo'
  have hzero := winning_pending_leaf_advance_zero hHN hH blue hwinq hp false hside
    (by simpa only [Board.get, hleft] using htarget)
    (by simpa only [Board.get, hleft] using hstrict)
  have hpzero : q.position.pending = some ⟨false, .advance 0⟩ := by
    simpa only [hzero] using hp
  have hMq : ∃ M : Managed N H blue b σ t mode other q.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target := by
    rw [hboard]
    exact ⟨Mv, hMv⟩
  obtain ⟨Mq, hMqfrom⟩ := hMq
  have hlast := winning_before_last_leaf_other_exhausted hHN hH blue hwinq
    (follow_mode_some hpq hmode) hpzero
    (by simpa only [hleft] using htarget) (by simpa only [hleft] using hstrict)
    (by simpa only [hleft] using hnext) (by simpa only [hleft] using hrootLast)
    (by simpa only [hleft] using hleafLast)
    (Mq.not_start ((Position.history_dataInvariant q).2.1 true).1)
  exact ⟨q, hpq, hpzero, hleft, by simpa only [hboard, Board.get] using hvr,
    by simpa only [hboard, Board.get] using hvsep, hlast, Mq, hMqfrom⟩

#print axioms inside_last_leaf_checkpoint

end Erdos591.Positive.Game.Payoff
