import ErdosProblems.Erdos118.Reused591.FreshNextLeaf
import ErdosProblems.Erdos118.Reused591.PreparedSelectionTransport

namespace Erdos118.Reused591

/-! # Reach the next saved selection and submit its original delayed reply -/

namespace Erdos591.Positive.Game.Relay.PreparedSelection

open Erdos591.Negative.Exact
open Payoff

theorem fire_at_next_leaf {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (side : Bool)
    (P : PreparedSelection N H blue b σ (p.position.board.get side))
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hstrict : (p.position.board.get side).leafIndex < P.labels.pivot)
    (hnext : ∀ x ∈ (p.position.board.get side).currentLabel,
      (p.position.board.get side).leafIndex < x → P.labels.pivot ≤ x)
    (hother : (p.position.board.get (!side)).relaxed = true)
    (hsep : ∀ x ∈ (p.position.board.get side).coordinates,
      x ≤ (p.position.board.get (!side)).coordinates.getLastD 0) :
    ∃ q target, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      (exactGame N blue).FollowStep σ H b P.target target ∧
      q.position.pending = none ∧ target.position.pending = none ∧
      (q.position.board.get side).relaxed = true ∧
      (q.position.board.get side).leafIndex = P.labels.pivot ∧
      (q.position.board.get side).currentLabel = P.lowerLabel ∧
      q.position.board.get (!side) = p.position.board.get (!side) ∧
      (∀ x ∈ (q.position.board.get (!side)).coordinates,
        x ≤ (q.position.board.get side).coordinates.getLastD 0) ∧
      LabeledWord.SameStructure (q.position.board.get side) (target.position.board.get P.side) ∧
      (target.position.board.get P.side).relaxed = true ∧
      (target.position.board.get P.side).rootLabel =
        (P.target.position.board.get P.side).rootLabel ∧
      (target.position.board.get P.side).currentLabel = P.labels.upper ∧
      (target.position.board.get P.side).leafIndex = P.labels.pivot ∧
      target.position.board.get (!P.side) = P.target.position.board.get (!P.side) := by
  obtain ⟨q, hpq, hqn, hqr, hqi, hqb, _hqm, hqo, hqsep⟩ :=
    winning_next_leaf_after_other hHN hH blue hwin side P.upto hstrict hnext hother hsep
  obtain ⟨as, has, hpool⟩ := follow_word_inputs_above_bound hpq side
  have hfresh : ∀ a ∈ as, a.2 ∈ H ∧ P.budget < a.2 := by
    intro a ha
    exact ⟨(hpool a ha).1, P.budget_lt_bound.trans (hpool a ha).2⟩
  have hup : LabeledWord.UpToLeaf P.labels.pivot (q.position.board.get side) :=
    ⟨(of_decide_eq_true hqr).2.1,
      by rw [← hqi]; exact (of_decide_eq_true hqr).2.2, hqi.le⟩
  let Q := P.move has hqb hfresh hup
  obtain ⟨target, hstep, htn, hcoords, htr, hto, htroot, htbody, htleaf⟩ :=
    Q.fire_full hHN ((Position.history_dataInvariant q).2.1 side).2 hqi
  have hshape : LabeledWord.SameStructure (q.position.board.get side)
      (target.position.board.get P.side) := by
    obtain ⟨xs, hxs⟩ := History.word_run q side
    obtain ⟨ys, hys⟩ := History.word_run target P.side
    exact LabeledWord.sameStructure_of_initial_runs hxs.run hys.run hcoords.symm
  have hcurrent : (q.position.board.get side).currentLabel = P.lowerLabel := Q.currentLabel
  have htcurrent : (target.position.board.get P.side).currentLabel = P.labels.upper := by
    change (target.position.board.get Q.side).currentLabel = Q.labels.upper
    simp [LabeledWord.currentLabel, htbody]
  exact ⟨q, target, hpq, hstep, hqn, htn, hqr, hqi, hcurrent, hqo, hqsep,
    hshape, htr, htroot, htcurrent, htleaf, hto⟩

#print axioms fire_at_next_leaf

end Erdos591.Positive.Game.Relay.PreparedSelection

end Erdos118.Reused591
