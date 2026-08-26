import ErdosProblems.Erdos591.PrepareBodyHistory

/-!
# Prepared replies persist through individual strategy moves

The saved marker remains a coordinate of the lower word, so all later
response inputs are above the saved upper budget. An unread selected
leaf prevents a finish and prevents an advance from leaving its body.
-/

namespace Erdos591.Positive.Game

open Erdos591.Negative.Exact
open Payoff

theorem follow_step_word_inputs_fresh {N H : Set ℕ} {blue : SimpleGraph G}
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p q : Concrete.Hist N} (h : (exactGame N blue).FollowStep σ H b p q) (side : Bool) :
    ∃ as, LabeledWord.LegalRun (p.position.board.get side) as (q.position.board.get side) ∧
      ∀ a ∈ as, a.2 ∈ H ∧ max p.position.bound (b p) < a.2 := by
  cases h.1 with
  | architect q hp hq =>
      have hnone := ((Concrete.kind_architect_iff (payoff blue) p).mp hp).1
      have hboard := (History.Next.position_next hq).board_eq_of_no_pending hnone
      exact ⟨[], by simpa [hboard] using LabeledWord.LegalRun.nil (p.position.board.get side),
        by simp⟩
  | builder u hp hu huH hub =>
      obtain ⟨r, hpend⟩ := (Concrete.kind_builder_iff (payoff blue) p).mp hp
      have hs := Concrete.response_spec hu
      have hr := hs.reply_spec hpend
      obtain ⟨as, has, hmem⟩ := hr.legal_run
        (fun x hx => (Nat.zero_le (b p)).trans_lt (hub x hx)) side
      exact ⟨as, has, fun a ha => ⟨huH (hmem a ha),
        max_lt (hs.fresh a.2 (hmem a ha)) (hub a.2 (hmem a ha))⟩⟩

namespace Relay.PreparedBody

variable {N H : Set ℕ} {blue : SimpleGraph G} {b : Concrete.Hist N → ℕ}
  {σ : (exactGame N blue).ArchitectStrategy} {w : LabeledWord}

theorem marker_mem (P : PreparedBody N H blue b σ w) : P.labels.marker ∈ w.coordinates := by
  rw [LabeledWord.runAtoms_coordinates P.run.run, (LabeledWord.read_spec P.firstRead).2]
  simp

theorem budget_lt_bound {p : Concrete.Hist N} {s : Bool}
    (P : PreparedBody N H blue b σ (p.position.board.get s)) : P.budget < p.position.bound := by
  exact P.labels.marker_fresh.2.trans_le ((Position.history_dataInvariant p).1 _
    (p.position.board.get_support_subset s (LabeledWord.coordinate_mem_support P.marker_mem))).2.2

theorem follow {p q : Concrete.Hist N} (s : Bool)
    (P : PreparedBody N H blue b σ (p.position.board.get s))
    (hHN : H ⊆ N) (hH : H.Infinite)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hstep : (exactGame N blue).FollowStep σ H b p q)
    (hbefore : p.position.board.get s ≠ q.position.board.get s →
      (p.position.board.get s).leafIndex < P.labels.pivot) :
    ∃ Q : PreparedBody N H blue b σ (q.position.board.get s),
      Q.target = P.target ∧ Q.side = P.side ∧ HEq Q.labels P.labels := by
  by_cases heq : p.position.board.get s = q.position.board.get s
  · rw [← heq]
    exact ⟨P, rfl, rfl, HEq.rfl⟩
  have hlt := hbefore heq
  have hnext := History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hstep)
  have hshape : LabeledWord.UpToLeaf P.labels.pivot (q.position.board.get s) ∧
      (q.position.board.get s).bodyLabels = (p.position.board.get s).bodyLabels := by
    cases hp : p.position.pending with
    | none => exact (heq (by rw [hnext.board_eq_of_no_pending hp])).elim
    | some r =>
        obtain ⟨u, hr⟩ := hnext.reply_of_pending hp
        have hside : s = r.side := by
          by_contra hn
          have hs : s = !r.side := Bool.eq_not_of_ne hn
          exact heq (by simpa [hs] using hr.other_eq.symm)
        cases r with
        | mk t command =>
            have hst : s = t := hside
            subst t
            cases command with
            | finish =>
                have hn := winning_pending_finish_not_pending hHN hH blue hwin hp rfl
                exact (hn (Or.inr ⟨P.upto.selected, P.labels.pivot, P.upto.mem, hlt⟩)).elim
            | advance d =>
                have hz := hr.advance_up_to_leaf ((Position.history_dataInvariant p).2.1 s).1
                  P.upto hlt
                exact ⟨hz.1, hz.2.1⟩
  obtain ⟨as, has, hpool⟩ := follow_step_word_inputs_fresh hstep s
  have hfresh : ∀ a ∈ as, a.2 ∈ H ∧ P.budget < a.2 := by
    intro a ha
    exact ⟨(hpool a ha).1, P.budget_lt_bound.trans
      ((le_max_left _ _).trans_lt (hpool a ha).2)⟩
  exact ⟨P.move has hshape.2 hfresh hshape.1, rfl, rfl, HEq.rfl⟩

#print axioms follow

end Relay.PreparedBody

end Erdos591.Positive.Game
