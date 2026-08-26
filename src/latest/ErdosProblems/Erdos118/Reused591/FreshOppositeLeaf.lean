import ErdosProblems.Erdos118.Reused591.ManagedHandoff
import ErdosProblems.Erdos118.Reused591.FirstLeafGluingHistory

namespace Erdos118.Reused591

/-!
# One ordinary opposite selected leaf while the fresh word stays fixed

An unread selection in the fresh word prevents the opposite reply from
finishing. Its endpoint is a selected leaf or a selected-body marker;
in the latter case one positive body response supplies the first leaf.
No delayed-play or managed-word assumption is needed.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_first_leaf_after_marker {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (hn : p.position.pending = none)
    (hm : (p.position.board.get side).markerEvent = true) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      q.position.board.get (!side) = p.position.board.get (!side) ∧
      ∀ x ∈ (q.position.board.get (!side)).coordinates,
        x ≤ (q.position.board.get side).coordinates.getLastD 0 := by
  obtain ⟨v, d, hpv, hboard, hp, hd⟩ :=
    winning_request_at_marker hHN hH blue hwin side hn hm
  let B := max v.position.bound (b v)
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B 1 d (by omega) hd
  obtain ⟨q, _other, hvq, _ho, hqn, _hon, _hs, hqr, _hor, _hi, _hoi,
      _hb, _hob, hqo, _hoo⟩ := first_leaf_gluing hHN hH blue σ v v side side
        L L rfl rfl hp hp (by simpa only [hboard] using hm)
        (by simpa only [hboard] using hm) (LabeledWord.SameStructure.refl _) le_rfl le_rfl
  exact ⟨q, (Relation.ReflTransGen.single hpv).tail hvq, hqn, hqr,
    by simpa only [hboard] using hqo,
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hvq).reply_separation hp⟩

theorem winning_next_opposite_leaf {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (hrel : (p.position.board.get side).relaxed = true)
    (hsep : ∀ x ∈ (p.position.board.get (!side)).coordinates,
      x ≤ (p.position.board.get side).coordinates.getLastD 0)
    (hremain : Macro.Pending (p.position.board.get side)) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get (!side)).relaxed = true ∧
      q.position.board.get side = p.position.board.get side ∧
      ∀ x ∈ (q.position.board.get side).coordinates,
        x ≤ (q.position.board.get (!side)).coordinates.getLastD 0 := by
  have hw := ((Position.history_dataInvariant p).2.1 side).1
  have hlive := LabeledWord.relaxed_not_terminal hw.2.1 hw.2.2 hrel
  obtain ⟨v, r, hpv, hboard, hp⟩ :=
    request_on_live_board σ p (Board.not_done_of_live hlive)
  have hwinV := hwin.of_reachable (exactGame N blue) hpv
  have hside : r.side = !side := winning_pending_switch hHN hH blue hwinV hp side
    (by simpa only [hboard] using hrel) (by simpa only [hboard] using hsep)
  have hk : (exactGame N blue).kind v = .builder :=
    (Concrete.kind_builder_iff (payoff blue) v).mpr ⟨r, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH v hk (b v)
  have hs := FiniteResponseGame.FollowStep.builder (exactGame N blue) σ v u hk hu huH hub
  let w := (exactGame N blue).response v u
  have hpw : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p w := hpv.tail hs
  have hwinW := hwin.of_reachable (exactGame N blue) hpw
  have hnext := History.Next.position_next (FiniteResponseGame.FollowStep.next
    (exactGame N blue) hs)
  obtain ⟨u', hr⟩ := hnext.reply_of_pending hp
  have hwo : w.position.board.get side = p.position.board.get side := by
    simpa only [hside, Bool.not_not, hboard] using hr.other_eq
  have hwn : w.position.pending = none := hnext.no_pending_after_reply hp
  have hwsep : ∀ x ∈ (w.position.board.get side).coordinates,
      x ≤ (w.position.board.get (!side)).coordinates.getLastD 0 := by
    simpa only [hside, Bool.not_not] using
      (FiniteResponseGame.FollowStep.next (exactGame N blue) hs).reply_separation hp
  have hwterm : (w.position.board.get (!side)).terminal = false := by
    cases he : (w.position.board.get (!side)).terminal with
    | false => rfl
    | true =>
        have hn := winning_not_pending_of_other_complete hHN hH blue hwinW side he
        exact (hn (by simpa only [hwo] using hremain)).elim
  have hevent : (w.position.board.get (!side)).relaxed = true ∨
      (w.position.board.get (!side)).markerEvent = true := by
    have hev : (w.position.board.get r.side).event = true := hr.end_event
    rw [hside] at hev
    simpa only [LabeledWord.event, hwterm, Bool.false_or, Bool.or_eq_true] using hev
  rcases hevent with hwr | hwm
  · exact ⟨w, hpw, hwn, hwr, hwo, hwsep⟩
  · obtain ⟨q, hwq, hqn, hqr, hqo, hqsep⟩ :=
      winning_first_leaf_after_marker hHN hH blue hwinW (!side) hwn hwm
    exact ⟨q, hpw.trans hwq, hqn, hqr,
      (by simpa only [Bool.not_not] using hqo.trans (by simpa only [Bool.not_not] using hwo)),
      (by simpa only [Bool.not_not] using hqsep)⟩

#print axioms winning_first_leaf_after_marker
#print axioms winning_next_opposite_leaf

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
