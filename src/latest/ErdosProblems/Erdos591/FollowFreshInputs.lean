import ErdosProblems.Erdos591.PreparedBodyTransport

/-! # All inputs on an actual path exceed its initial history bound -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem follow_word_inputs_above_bound {N H : Set ℕ} {blue : SimpleGraph G}
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p q : Concrete.Hist N}
    (h : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q) (side : Bool) :
    ∃ as, LabeledWord.LegalRun (p.position.board.get side) as (q.position.board.get side) ∧
      ∀ a ∈ as, a.2 ∈ H ∧ p.position.bound < a.2 := by
  induction h with
  | refl => exact ⟨[], .nil _, by simp⟩
  | @tail q t hpq hqt ih =>
      obtain ⟨xs, hx, hxs⟩ := ih
      obtain ⟨ys, hy, hys⟩ := follow_step_word_inputs_fresh hqt side
      have hbound := (History.reachable_word_extension (follow_history_path hpq)).1
      refine ⟨xs ++ ys, hx.append hy, ?_⟩
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hxs a ha
      · exact ⟨(hys a ha).1, hbound.trans_lt ((le_max_left _ _).trans_lt (hys a ha).2)⟩

#print axioms follow_word_inputs_above_bound

end Erdos591.Positive.Game.Payoff
