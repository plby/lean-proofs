import ErdosProblems.Erdos118.Reused591.BeforeBody
import ErdosProblems.Erdos118.Reused591.FinishBodyLabels

namespace Erdos118.Reused591

/-!
# Reaching a selected body's pending architect request

A winning finite continuation must eventually read every selected body.
The first reply that crosses a prescribed selected index must start at
that body's marker, and its request has positive size. Retaining only
the preceding history leaves the label and marker free to choose.
-/

namespace Erdos591.Positive.Game

theorem path_has_boundary {α : Type*} {R : α → α → Prop} (P : α → Prop)
    {a z : α} (hpath : Relation.ReflTransGen R a z) (ha : P a) (hz : ¬ P z) :
    ∃ p q, Relation.ReflTransGen R a p ∧ R p q ∧ P p ∧ ¬ P q := by
  classical
  revert hz
  induction hpath with
  | refl => exact fun hz => (hz ha).elim
  | @tail p q hap hpq ih =>
      intro hq
      by_cases hp : P p
      · exact ⟨p, q, hap, hpq, hp, hq⟩
      · exact ih hp

namespace Position

theorem Next.board_eq_of_no_pending {N : Set ℕ} {p q : Position} (h : Next N q p)
    (hp : p.pending = none) : q.board = p.board := by
  cases h with
  | request _ _ _ _ _ _ _ => rfl
  | reply p r u board hpend _ _ _ => simp [hp] at hpend

theorem Next.reply_of_pending {N : Set ℕ} {p q : Position} (h : Next N q p)
    {r : Request} (hp : p.pending = some r) : ∃ u, Reply p.board r u q.board := by
  cases h with
  | request p mode s ht _ _ _ => simp [hp] at ht
  | reply p s u board hpend hr _ _ =>
      have heq : s = r := Option.some.inj (hpend.symm.trans hp)
      exact ⟨u, heq ▸ hr⟩

end Position

namespace Payoff

open Erdos591.Negative.Exact

theorem winning_reach_body_marker {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool) (i : ℕ)
    (hstart : (p.position.board.get side).parser ≠ .start)
    (hi : LabeledWord.BeforeBody i (p.position.board.get side)) :
    ∃ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨side, .advance d⟩ ∧ 0 < d ∧
      (q.position.board.get side).markerEvent = true ∧
      (q.position.board.get side).bodyLabels.length + 1 = i := by
  obtain ⟨z, hpz, _, hdone, _⟩ := winning_continuation hHN hH blue hwin
  have hznot : ¬ LabeledWord.BeforeBody i (z.position.board.get side) := by
    intro hz
    have ht := z.position.board.terminal_of_done hdone side
    have hf := hz.not_terminal ((Position.history_dataInvariant z).2.1 side).1
    simp [ht] at hf
  obtain ⟨q, t, hpq, hqt, hbefore, hafter⟩ :=
    path_has_boundary (fun q : Concrete.Hist N =>
      LabeledWord.BeforeBody i (q.position.board.get side)) hpz hi hznot
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
        have hother := hreply.other_eq
        exact hafter (by simpa [heq, hother] using hbefore)
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
              exact ⟨q, d, hpq, hpend, hpos, hm⟩

#print axioms winning_reach_body_marker

end Payoff

end Erdos591.Positive.Game

end Erdos118.Reused591
