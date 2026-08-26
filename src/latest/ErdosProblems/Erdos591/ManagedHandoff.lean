import ErdosProblems.Erdos591.ManagedOrigins
import ErdosProblems.Erdos591.BoundaryRequests

/-!
# The next opposite selected leaf, with its delayed play retained

A fresh selected leaf forces the other side's next request. Its managed
response stays unfinished, so it stops at a selected leaf or body marker.
At a marker one more managed body response reaches its first leaf.
-/

namespace Erdos591.Positive.Game

theorem Reply.end_event {board last : Board} {r : Request} {u : Finset ℕ}
    (hr : Reply board r u last) : (last.get r.side).event = true := by
  cases hr with
  | finish side u w hlegal hrun =>
      have ht : w.terminal = true := LabeledWord.finishParser.run_stopped hrun
      simp [LabeledWord.event, ht]
  | advance side d u w hlegal hrun =>
      obtain ⟨labels, n, rest, last, _hxs, _hlen, heq, _hc, _hlt, hevent, _hparsed⟩ :=
        Advance.run_result ⟨board.get side, hlegal.1⟩ d (u.sort (· ≤ ·)) (.remainder w) hrun
      have hw : w = last := Advance.State.remainder.inj heq
      simpa [hw] using hevent

namespace Relay

open Erdos591.Negative.Exact
open Payoff

theorem managed_next_opposite_leaf_from {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool)
    (hrel : (p.position.board.get side).relaxed = true)
    (hsep : ∀ y ∈ (p.position.board.get (!side)).coordinates,
      y ≤ (p.position.board.get side).coordinates.getLastD 0)
    (hPending : Macro.Pending (p.position.board.get side))
    {t mode : Bool} {other : LabeledWord} (origin : Concrete.Hist N)
    (hmanaged : ∃ M : Managed N H blue b σ t mode other (p.position.board.get (!side)),
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get (!side)).relaxed = true ∧
      q.position.board.get side = p.position.board.get side ∧
      (∀ y ∈ (q.position.board.get side).coordinates,
        y ≤ (q.position.board.get (!side)).coordinates.getLastD 0) ∧
      ∃ M : Managed N H blue b σ t mode other (q.position.board.get (!side)),
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
  obtain ⟨M, hfrom⟩ := hmanaged
  have hlive := M.unfinished ((Position.history_dataInvariant p).2.1 (!side)).1
  obtain ⟨q, r, hpq, hboard, hp⟩ := request_on_live_board σ p (Board.not_done_of_live hlive)
  have hwinq := hwin.of_reachable (exactGame N blue) hpq
  have hside : r.side = !side := winning_pending_switch hHN hH blue hwinq hp side
    (by simpa only [hboard] using hrel) (by simpa only [hboard] using hsep)
  have hMq : ∃ Q : Managed N H blue b σ t mode other (q.position.board.get r.side),
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin Q.target := by
    rw [hside, hboard]
    exact ⟨M, hfrom⟩
  obtain ⟨Mq, hMqfrom⟩ := hMq
  have hnot : ¬ BothLast q.position.board := by
    intro hlast
    exact hlast side (by simpa only [hboard] using hPending)
  obtain ⟨v, hqv, hvn, hvo, Mv, hMvfrom⟩ :=
    Mq.respond_from hHN hH blue hwinq hp hnot origin hMqfrom
  have hpv := hpq.tail hqv
  have hwinv := hwin.of_reachable (exactGame N blue) hpv
  have hn := History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hqv)
  obtain ⟨u, hr⟩ := hn.reply_of_pending hp
  have hevent := hr.end_event
  have hvterm := Mv.unfinished ((Position.history_dataInvariant v).2.1 r.side).1
  have hvo' : v.position.board.get side = p.position.board.get side := by
    simpa only [hside, Bool.not_not, hboard] using hvo
  have hsepv : ∀ y ∈ (v.position.board.get side).coordinates,
      y ≤ (v.position.board.get (!side)).coordinates.getLastD 0 := by
    simpa only [hside, Bool.not_not] using
      (FiniteResponseGame.FollowStep.next (exactGame N blue) hqv).reply_separation hp
  have hM : ∃ Q : Managed N H blue b σ t mode other (v.position.board.get (!side)),
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin Q.target := by
    rw [← hside]
    exact ⟨Mv, hMvfrom⟩
  have hvterm' : (v.position.board.get (!side)).terminal = false := by
    simpa only [hside] using hvterm
  have hev : (v.position.board.get (!side)).relaxed = true ∨
      (v.position.board.get (!side)).markerEvent = true := by
    simpa only [LabeledWord.event, hside, hvterm', Bool.false_or, Bool.or_eq_true] using hevent
  rcases hev with hvr | hvm
  · exact ⟨v, hpv, hvn, hvr, hvo', hsepv, hM⟩
  · obtain ⟨Q, hQ⟩ := hM
    obtain ⟨z, hvz, hzn, hzr, hzo, hzsep, Mz, hMz⟩ :=
      Q.first_body_from_fresh hHN hH blue hwinv (!side) hvn hvm origin hQ
    exact ⟨z, hpv.trans hvz, hzn, hzr,
      (by simpa only [Bool.not_not] using hzo.trans (by simpa only [Bool.not_not] using hvo')),
      (by simpa only [Bool.not_not] using hzsep), Mz, hMz⟩

#print axioms managed_next_opposite_leaf_from

end Relay

end Erdos591.Positive.Game
