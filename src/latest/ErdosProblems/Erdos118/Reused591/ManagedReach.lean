import ErdosProblems.Erdos118.Reused591.ManagedGuard

namespace Erdos118.Reused591

/-!
# Reaching a selected marker or leaf while the opposite word stays managed

The stopping predicates cannot disappear at a finish in a winning play.
An advance first crosses a body index at its pending marker, or reaches
the prescribed leaf exactly. The delayed opposite play retains its origin.
-/

namespace Erdos591.Positive.Game.Relay

open Erdos591.Negative.Exact
open Payoff

theorem managed_reach_body_marker_from {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool) (i : ℕ)
    (hstart : (p.position.board.get side).parser ≠ .start)
    (hi : LabeledWord.BeforeBody i (p.position.board.get side))
    {t mode : Bool} {other : LabeledWord} (origin : Concrete.Hist N)
    (hmanaged : ∃ M : Managed N H blue b σ t mode other (p.position.board.get (!side)),
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target) :
    ∃ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨side, .advance d⟩ ∧ 0 < d ∧
      (q.position.board.get side).markerEvent = true ∧
      (q.position.board.get side).bodyLabels.length + 1 = i ∧
      ∃ M : Managed N H blue b σ t mode other (q.position.board.get (!side)),
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
  obtain ⟨q, z, r, hpq, hqz, hp, hside, hbefore, hafter, hM⟩ :=
    managed_guard_boundary_from hHN hH blue side (LabeledWord.BeforeBody i)
      (fun _ h => Or.inl ⟨i, h⟩) origin p hwin hi hmanaged
  have hnext := History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hqz)
  obtain ⟨u, hr⟩ := hnext.reply_of_pending hp
  have hwinq := hwin.of_reachable (exactGame N blue) hpq
  obtain ⟨as, has, _⟩ := (History.reachable_word_extension (follow_history_path hpq)).2 side
  have hstartq := has.parser_ne_start hstart
  cases r with
  | mk s command =>
      have heq : s = side := hside
      subst s
      cases command with
      | finish =>
          have hle := winning_pending_finish_no_future_body hHN hH blue hwinq hp rfl
            hstartq i hbefore.1
          exact (Nat.not_lt_of_ge hle hbefore.2).elim
      | advance d =>
          have hm := (hr.advance_before_body_or_marker hbefore hstartq).resolve_left hafter
          exact ⟨q, d, hpq, hp, winning_pending_marker_size_pos hHN hH blue hwinq hp hm.1,
            hm.1, hm.2, hM⟩

theorem managed_reach_selected_leaf_from {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool) (j : ℕ)
    (hj : LabeledWord.UpToLeaf j (p.position.board.get side))
    (hlt : (p.position.board.get side).leafIndex < j)
    {t mode : Bool} {other : LabeledWord} (origin : Concrete.Hist N)
    (hmanaged : ∃ M : Managed N H blue b σ t mode other (p.position.board.get (!side)),
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).leafIndex = j ∧
      (q.position.board.get side).bodyLabels = (p.position.board.get side).bodyLabels ∧
      (q.position.board.get side).bodyMarker = (p.position.board.get side).bodyMarker ∧
      (∀ y ∈ (q.position.board.get (!side)).coordinates,
        y ≤ (q.position.board.get side).coordinates.getLastD 0) ∧
      ∃ M : Managed N H blue b σ t mode other (q.position.board.get (!side)),
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
  let P (w : LabeledWord) : Prop := LabeledWord.UpToLeaf j w ∧ w.leafIndex < j ∧
    w.bodyLabels = (p.position.board.get side).bodyLabels ∧
    w.bodyMarker = (p.position.board.get side).bodyMarker
  have hPpending : ∀ w, P w → Macro.Pending w :=
    fun _ h => Or.inr ⟨h.1.selected, j, h.1.mem, h.2.1⟩
  obtain ⟨q, z, r, hpq, hqz, hp, hside, hbefore, hafter, hM⟩ :=
    managed_guard_boundary_from hHN hH blue side P hPpending origin p hwin
      ⟨hj, hlt, rfl, rfl⟩ hmanaged
  have hnext := History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hqz)
  obtain ⟨u, hr⟩ := hnext.reply_of_pending hp
  have hwinq := hwin.of_reachable (exactGame N blue) hpq
  cases r with
  | mk s command =>
      have heq : s = side := hside
      subst s
      cases command with
      | finish =>
          have hn := winning_pending_finish_not_pending hHN hH blue hwinq hp rfl
          exact (hn (hPpending _ hbefore)).elim
      | advance d =>
          have hz := hr.advance_up_to_leaf ((Position.history_dataInvariant q).2.1 side).1
            hbefore.1 hbefore.2.1
          have hlabels := hz.2.1.trans hbefore.2.2.1
          have hmarker := hz.2.2.trans hbefore.2.2.2
          have heq : (z.position.board.get side).leafIndex = j := by
            by_contra hn
            exact hafter ⟨hz.1, lt_of_le_of_ne hz.1.before hn, hlabels, hmarker⟩
          refine ⟨z, hpq.tail hqz, hnext.no_pending_after_reply hp,
            hz.1.relaxed_of_eq ((Position.history_dataInvariant z).2.1 side).1 heq,
            heq, hlabels, hmarker,
            (FiniteResponseGame.FollowStep.next (exactGame N blue) hqz).reply_separation hp, ?_⟩
          rw [hr.other_eq]
          exact hM

theorem managed_reach_selected_leaf_le_from {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (j : ℕ) (hp : p.position.pending = none)
    (hj : LabeledWord.UpToLeaf j (p.position.board.get side))
    (hsep : ∀ y ∈ (p.position.board.get (!side)).coordinates,
      y ≤ (p.position.board.get side).coordinates.getLastD 0)
    {t mode : Bool} {other : LabeledWord} (origin : Concrete.Hist N)
    (hmanaged : ∃ M : Managed N H blue b σ t mode other (p.position.board.get (!side)),
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).leafIndex = j ∧
      (q.position.board.get side).bodyLabels = (p.position.board.get side).bodyLabels ∧
      (q.position.board.get side).bodyMarker = (p.position.board.get side).bodyMarker ∧
      (∀ y ∈ (q.position.board.get (!side)).coordinates,
        y ≤ (q.position.board.get side).coordinates.getLastD 0) ∧
      ∃ M : Managed N H blue b σ t mode other (q.position.board.get (!side)),
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target := by
  rcases lt_or_eq_of_le hj.before with hlt | heq
  · exact managed_reach_selected_leaf_from hHN hH blue hwin side j hj hlt origin hmanaged
  · exact ⟨p, .refl, hp, hj.relaxed_of_eq ((Position.history_dataInvariant p).2.1 side).1 heq,
      heq, rfl, rfl, hsep, hmanaged⟩

#print axioms managed_reach_body_marker_from
#print axioms managed_reach_selected_leaf_from
#print axioms managed_reach_selected_leaf_le_from

end Erdos591.Positive.Game.Relay

end Erdos118.Reused591
