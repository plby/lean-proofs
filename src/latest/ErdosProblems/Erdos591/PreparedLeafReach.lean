import ErdosProblems.Erdos591.PreparedLeafTransport
import ErdosProblems.Erdos591.FollowFreshInputs

/-! # Reach a saved body's last selected leaf while retaining its actual upper request -/

namespace Erdos591.Positive.Game.Relay.PreparedLeaf

open Erdos591.Negative.Exact
open Payoff

theorem reach_last {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N} (side : Bool)
    (P : PreparedLeaf N H blue b σ (p.position.board.get side))
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (hn : p.position.pending = none)
    (hsep : ∀ y ∈ (p.position.board.get (!side)).coordinates,
      y ≤ (p.position.board.get side).coordinates.getLastD 0) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (∀ y ∈ (q.position.board.get (!side)).coordinates,
        y ≤ (q.position.board.get side).coordinates.getLastD 0) ∧
      ∃ Q : PreparedLeaf N H blue b σ (q.position.board.get side),
        Q.target = P.target ∧ Q.side = P.side ∧ HEq Q.labels P.labels ∧ Q.stem = P.stem ∧
          (q.position.board.get side).leafIndex = Q.labels.pivot := by
  obtain ⟨q, hpq, hqn, hqr, hqi, hqb, _hqm, hqsep⟩ :=
    winning_reach_selected_leaf_le_fresh hHN hH blue hwin side P.labels.pivot hn P.upto hsep
  obtain ⟨as, has, hpool⟩ := follow_word_inputs_above_bound hpq side
  have hfresh : ∀ a ∈ as, a.2 ∈ H ∧ P.budget < a.2 := by
    intro a ha
    exact ⟨(hpool a ha).1, P.budget_lt_bound.trans (hpool a ha).2⟩
  have hup : LabeledWord.UpToLeaf P.labels.pivot (q.position.board.get side) :=
    ⟨(of_decide_eq_true hqr).2.1, by rw [← hqi]; exact (of_decide_eq_true hqr).2.2, hqi.le⟩
  exact ⟨q, hpq, hqn, hqr, hqsep, P.move has hqb hfresh hup, rfl, rfl, HEq.rfl, rfl, hqi⟩

#print axioms reach_last

end Erdos591.Positive.Game.Relay.PreparedLeaf
