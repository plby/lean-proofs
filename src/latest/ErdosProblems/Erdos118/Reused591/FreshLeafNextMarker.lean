import ErdosProblems.Erdos118.Reused591.NextMarkerReplayHistory
import ErdosProblems.Erdos118.Reused591.BoundaryRequests
import ErdosProblems.Erdos118.Reused591.PendingNextLeaf

namespace Erdos118.Reused591

/-! # The actual opposite next-body request after a fresh selected leaf -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_next_body_after_fresh_leaf {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (hrel : (p.position.board.get side).relaxed = true)
    (hsep : ∀ y ∈ (p.position.board.get (!side)).coordinates,
      y ≤ (p.position.board.get side).coordinates.getLastD 0)
    (hother : (p.position.board.get (!side)).relaxed = true) {i : ℕ}
    (hbefore : LabeledWord.BeforeBody i (p.position.board.get (!side))) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.board = p.position.board ∧
      q.position.pending = some ⟨!side, .advance 0⟩ := by
  have hw := ((Position.history_dataInvariant p).2.1 side).1
  have hlive := LabeledWord.relaxed_not_terminal hw.2.1 hw.2.2 hrel
  obtain ⟨q, r, hpath, hboard, hp⟩ :=
    request_on_live_board σ p (Board.not_done_of_live hlive)
  have hwinQ := hwin.of_reachable (exactGame N blue) hpath
  have hs := winning_pending_switch hHN hH blue hwinQ hp side
    (by simpa only [hboard] using hrel) (by simpa only [hboard] using hsep)
  have hr := winning_pending_root_advance_zero hHN hH blue hwinQ hp (!side) hs
    (by simpa only [hboard] using hother) (by simpa only [hboard] using hbefore)
  exact ⟨q, hpath, hboard, by simpa only [hr] using hp⟩

#print axioms winning_next_body_after_fresh_leaf

theorem winning_next_selection_after_fresh_leaf {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (hrel : (p.position.board.get side).relaxed = true)
    (hsep : ∀ y ∈ (p.position.board.get (!side)).coordinates,
      y ≤ (p.position.board.get side).coordinates.getLastD 0)
    (hother : (p.position.board.get (!side)).relaxed = true)
    (hpending : Macro.Pending (p.position.board.get (!side))) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.board = p.position.board ∧
      q.position.pending = some ⟨!side, .advance 0⟩ := by
  rcases hpending with ⟨i, hi, hlt⟩ | ⟨hsel, j, hj, hlt⟩
  · exact winning_next_body_after_fresh_leaf hHN hH blue hwin side hrel hsep hother ⟨hi, hlt⟩
  · exact winning_next_leaf_request_after_other hHN hH blue hwin (!side)
      ⟨hsel, hj, hlt.le⟩ hlt (by simpa only [Bool.not_not] using hrel)
      (by simpa only [Bool.not_not] using hsep)

#print axioms winning_next_selection_after_fresh_leaf

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
