import ErdosProblems.Erdos591.TargetLeaf
import ErdosProblems.Erdos591.ReachBodyMarker
import ErdosProblems.Erdos591.FinishRestriction
import ErdosProblems.Erdos591.ReplySeparation

/-!
# Stopping a winning continuation at a prescribed selected leaf

Track one unread selected leaf in the current body. A finish would
violate the checked pending-index restriction, and an advance cannot
pass the leaf. The first loss of the strict-before invariant in a finite
winning continuation is therefore a reply ending exactly at that leaf.
-/

namespace Erdos591.Positive.Game

theorem Position.Next.no_pending_after_reply {N : Set ℕ} {p q : Position}
    (h : Position.Next N q p) {r : Request} (hp : p.pending = some r) :
    q.pending = none := by
  cases h with
  | request p mode s ht _ _ _ => simp [hp] at ht
  | reply _ _ _ _ _ _ _ _ => rfl

namespace Payoff

open Erdos591.Negative.Exact

theorem winning_reach_selected_leaf_fresh {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool) (j : ℕ)
    (hj : LabeledWord.UpToLeaf j (p.position.board.get side))
    (hlt : (p.position.board.get side).leafIndex < j) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).leafIndex = j ∧
      (q.position.board.get side).bodyLabels = (p.position.board.get side).bodyLabels ∧
      (q.position.board.get side).bodyMarker = (p.position.board.get side).bodyMarker ∧
      ∀ y ∈ (q.position.board.get (!side)).coordinates,
        y ≤ (q.position.board.get side).coordinates.getLastD 0 := by
  let P (q : Concrete.Hist N) : Prop :=
    LabeledWord.UpToLeaf j (q.position.board.get side) ∧
      (q.position.board.get side).leafIndex < j ∧
      (q.position.board.get side).bodyLabels = (p.position.board.get side).bodyLabels ∧
      (q.position.board.get side).bodyMarker = (p.position.board.get side).bodyMarker
  obtain ⟨z, hpz, _, hdone, _⟩ := winning_continuation hHN hH blue hwin
  have hznot : ¬ P z := by
    intro hz
    obtain ⟨r, k, hparse⟩ := hz.1.parser_leaves ((Position.history_dataInvariant z).2.1 side).1
    have ht := z.position.board.terminal_of_done hdone side
    simp [LabeledWord.terminal, hparse] at ht
  obtain ⟨q, t, hpq, hqt, hbefore, hafter⟩ :=
    path_has_boundary P hpz ⟨hj, hlt, rfl, rfl⟩ hznot
  have hnext := History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hqt)
  have hwinq := hwin.of_reachable (exactGame N blue) hpq
  cases hpend : q.position.pending with
  | none =>
      have hboard := hnext.board_eq_of_no_pending hpend
      exact (hafter (by simpa [P, hboard] using hbefore)).elim
  | some r =>
      obtain ⟨u, hreply⟩ := hnext.reply_of_pending hpend
      have hside : side = r.side := by
        by_contra hn
        have heq : side = !r.side := Bool.eq_not_of_ne hn
        have hother := hreply.other_eq
        exact hafter (by simpa [P, heq, hother] using hbefore)
      cases r with
      | mk s command =>
          have hse : side = s := hside
          subst s
          cases command with
          | finish =>
              have hn := winning_pending_finish_not_pending hHN hH blue hwinq hpend rfl
              exact (hn (Or.inr ⟨hbefore.1.selected, j, hbefore.1.mem, hbefore.2.1⟩)).elim
          | advance d =>
              have hwq := ((Position.history_dataInvariant q).2.1 side).1
              have hv := hreply.advance_up_to_leaf hwq hbefore.1 hbefore.2.1
              have hlabels := hv.2.1.trans hbefore.2.2.1
              have hmarker := hv.2.2.trans hbefore.2.2.2
              have heq : (t.position.board.get side).leafIndex = j := by
                by_contra hn
                exact hafter ⟨hv.1, lt_of_le_of_ne hv.1.before hn, hlabels, hmarker⟩
              have hrel := hv.1.relaxed_of_eq ((Position.history_dataInvariant t).2.1 side).1 heq
              exact ⟨t, hpq.tail hqt, hnext.no_pending_after_reply hpend,
                hrel, heq, hlabels, hmarker,
                (FiniteResponseGame.FollowStep.next (exactGame N blue) hqt).reply_separation hpend⟩

theorem winning_reach_selected_leaf {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool) (j : ℕ)
    (hj : LabeledWord.UpToLeaf j (p.position.board.get side))
    (hlt : (p.position.board.get side).leafIndex < j) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).leafIndex = j ∧
      (q.position.board.get side).bodyLabels = (p.position.board.get side).bodyLabels ∧
      (q.position.board.get side).bodyMarker = (p.position.board.get side).bodyMarker := by
  obtain ⟨q, hp, hn, hr, hi, hb, hm, _⟩ :=
    winning_reach_selected_leaf_fresh hHN hH blue hwin side j hj hlt
  exact ⟨q, hp, hn, hr, hi, hb, hm⟩

theorem winning_reach_selected_leaf_le {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool) (j : ℕ)
    (hp : p.position.pending = none) (hj : LabeledWord.UpToLeaf j (p.position.board.get side)) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).leafIndex = j ∧
      (q.position.board.get side).bodyLabels = (p.position.board.get side).bodyLabels ∧
      (q.position.board.get side).bodyMarker = (p.position.board.get side).bodyMarker := by
  rcases lt_or_eq_of_le hj.before with hlt | heq
  · exact winning_reach_selected_leaf hHN hH blue hwin side j hj hlt
  · exact ⟨p, .refl, hp,
      hj.relaxed_of_eq ((Position.history_dataInvariant p).2.1 side).1 heq, heq, rfl, rfl⟩

#print axioms winning_reach_selected_leaf
#print axioms winning_reach_selected_leaf_fresh
#print axioms winning_reach_selected_leaf_le

theorem winning_reach_selected_leaf_le_fresh {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (side : Bool) (j : ℕ) (hp : p.position.pending = none)
    (hj : LabeledWord.UpToLeaf j (p.position.board.get side))
    (hsep : ∀ y ∈ (p.position.board.get (!side)).coordinates,
      y ≤ (p.position.board.get side).coordinates.getLastD 0) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).leafIndex = j ∧
      (q.position.board.get side).bodyLabels = (p.position.board.get side).bodyLabels ∧
      (q.position.board.get side).bodyMarker = (p.position.board.get side).bodyMarker ∧
      ∀ y ∈ (q.position.board.get (!side)).coordinates,
        y ≤ (q.position.board.get side).coordinates.getLastD 0 := by
  rcases lt_or_eq_of_le hj.before with hlt | heq
  · exact winning_reach_selected_leaf_fresh hHN hH blue hwin side j hj hlt
  · exact ⟨p, .refl, hp,
      hj.relaxed_of_eq ((Position.history_dataInvariant p).2.1 side).1 heq,
      heq, rfl, rfl, hsep⟩

#print axioms winning_reach_selected_leaf_le_fresh

end Payoff

end Erdos591.Positive.Game
