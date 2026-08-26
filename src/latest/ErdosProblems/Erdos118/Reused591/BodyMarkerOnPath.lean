import ErdosProblems.Erdos118.Reused591.ReachBodyMarker

namespace Erdos118.Reused591

/-!
# A selected-marker request retained inside a prescribed finite path

The first crossing of an unread selected body is a positive marker
reply. Both pieces of the original path are retained, so invariants
at the later endpoint can be transported back to the marker request.
-/

namespace Erdos591.Positive.Game

theorem path_has_boundary_with_tail {α : Type*} {R : α → α → Prop}
    (P : α → Prop) {a z : α} (hpath : Relation.ReflTransGen R a z)
    (ha : P a) (hz : ¬ P z) :
    ∃ p q, Relation.ReflTransGen R a p ∧ R p q ∧ P p ∧ ¬ P q ∧
      Relation.ReflTransGen R q z := by
  classical
  revert hz
  induction hpath with
  | refl => exact fun hz => (hz ha).elim
  | @tail p q hap hpq ih =>
      intro hq
      by_cases hp : P p
      · exact ⟨p, q, hap, hpq, hp, hq, .refl⟩
      · obtain ⟨v, w, hav, hvw, hv, hw, hwp⟩ := ih hp
        exact ⟨v, w, hav, hvw, hv, hw, hwp.tail hpq⟩

namespace Payoff

open Erdos591.Negative.Exact

theorem winning_body_marker_on_path {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p z : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (i : ℕ)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z)
    (hstart : (p.position.board.get side).parser ≠ .start)
    (hi : LabeledWord.BeforeBody i (p.position.board.get side))
    (hz : ¬ LabeledWord.BeforeBody i (z.position.board.get side)) :
    ∃ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) q z ∧
      q.position.pending = some ⟨side, .advance d⟩ ∧ 0 < d ∧
      (q.position.board.get side).markerEvent = true ∧
      (q.position.board.get side).bodyLabels.length + 1 = i := by
  obtain ⟨q, t, hpq, hqt, hbefore, hafter, htz⟩ :=
    path_has_boundary_with_tail (fun q : Concrete.Hist N =>
      LabeledWord.BeforeBody i (q.position.board.get side)) hpath hi hz
  have hnext := History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hqt)
  have hwinq := hwin.of_reachable (exactGame N blue) hpq
  obtain ⟨as, has, _⟩ := (History.reachable_word_extension (follow_history_path hpq)).2 side
  have hstartq := has.parser_ne_start hstart
  cases hpend : q.position.pending with
  | none =>
      have hboard := hnext.board_eq_of_no_pending hpend
      exact (hafter (by simpa [hboard] using hbefore)).elim
  | some r =>
      obtain ⟨u, hreply⟩ := hnext.reply_of_pending hpend
      have hside : side = r.side := by
        by_contra hn
        have heq : side = !r.side := Bool.eq_not_of_ne hn
        exact hafter (by simpa [heq, hreply.other_eq] using hbefore)
      cases r with
      | mk s command =>
          have hse : side = s := hside
          subst s
          cases command with
          | finish =>
              have hle := winning_pending_finish_no_future_body hHN hH blue hwinq hpend rfl
                hstartq i hbefore.1
              exact (Nat.not_lt_of_ge hle hbefore.2).elim
          | advance d =>
              have hm := (hreply.advance_before_body_or_marker hbefore hstartq).resolve_left hafter
              have hpos := winning_pending_marker_size_pos hHN hH blue hwinq hpend hm.1
              exact ⟨q, d, hpq, (Relation.ReflTransGen.single hqt).trans htz,
                hpend, hpos, hm⟩

#print axioms winning_body_marker_on_path

end Payoff

end Erdos591.Positive.Game

end Erdos118.Reused591
