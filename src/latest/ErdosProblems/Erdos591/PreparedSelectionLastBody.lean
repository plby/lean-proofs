import ErdosProblems.Erdos591.PreparedSelectionTransport
import ErdosProblems.Erdos591.LastBodyEndpoint

/-! # Retain a saved last-body selection using its proved endpoint index -/

namespace Erdos591.Positive.Game.Relay.PreparedSelection

open Erdos591.Negative.Exact
open Payoff

theorem move_of_last_body {N H : Set ℕ} {blue : SimpleGraph G}
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p q : Concrete.Hist N} (side : Bool)
    (P : PreparedSelection N H blue b σ (p.position.board.get side))
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q)
    (hroot : ∀ i ∈ (p.position.board.get side).rootLabel,
      i ≤ (p.position.board.get side).bodyLabels.length)
    (hrel : (q.position.board.get side).relaxed = true)
    (hbefore : (q.position.board.get side).leafIndex ≤ P.labels.pivot) :
    ∃ Q : PreparedSelection N H blue b σ (q.position.board.get side),
      Q.target = P.target ∧ Q.side = P.side ∧ Q.stem = P.stem ∧
        Q.lowerLabel = P.lowerLabel ∧ Q.labels.pivot = P.labels.pivot ∧
        Q.labels.upper = P.labels.upper := by
  obtain ⟨as, has, hpool⟩ := follow_word_inputs_above_bound hpath side
  have hstart := P.run.parser_ne_start (LabeledWord.read_parser_ne_start P.firstRead)
  have hbody := (has.last_body_relaxed_labels hstart hroot hrel).1
  have hcurrent : (q.position.board.get side).currentLabel =
      (p.position.board.get side).currentLabel := by simp only [LabeledWord.currentLabel, hbody]
  have hfresh : ∀ a ∈ as, a.2 ∈ H ∧ P.budget < a.2 := by
    intro a ha
    exact ⟨(hpool a ha).1, P.budget_lt_bound.trans (hpool a ha).2⟩
  have hup : LabeledWord.UpToLeaf P.labels.pivot (q.position.board.get side) :=
    ⟨(of_decide_eq_true hrel).2.1, hcurrent ▸ P.upto.mem, hbefore⟩
  exact ⟨P.move has hbody hfresh hup, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms move_of_last_body

end Erdos591.Positive.Game.Relay.PreparedSelection
