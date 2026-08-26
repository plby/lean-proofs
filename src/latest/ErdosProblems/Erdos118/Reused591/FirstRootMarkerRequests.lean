import ErdosProblems.Erdos118.Reused591.FirstRootPlan
import ErdosProblems.Erdos118.Reused591.FollowFreshInputs

namespace Erdos118.Reused591

/-!
# The two actual requests at a prescribed critical body

Reach the lower selected marker and replay the saved upper root.
Both body requests are issued before any label or marker is chosen.
-/

namespace Erdos591.Positive.Game.Relay.FirstRootPlan

open Erdos591.Negative.Exact
open Payoff

variable {N H : Set ℕ} {blue : SimpleGraph G} {b : Concrete.Hist N → ℕ}
  {σ : (exactGame N blue).ArchitectStrategy}

theorem fire_after {p q : Concrete.Hist N} (side : Bool)
    (R : FirstRootPlan N H blue b σ (p.position.board.get side))
    (hHN : H ⊆ N) (hH : H.Infinite)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q)
    (hm : (q.position.board.get side).markerEvent = true)
    (hindex : (q.position.board.get side).bodyLabels.length + 1 = R.labels.shared) :
    ∃ upper d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) R.target upper ∧
      upper.position.pending = some ⟨R.side, .advance d⟩ ∧ 0 < d ∧
      upper.position.board.get R.side = LabeledWord.rootRelabel R.labels.upper
        (q.position.board.get side) ∧
      (upper.position.board.get R.side).markerEvent = true ∧
      (upper.position.board.get R.side).NoRootPassed ∧
      upper.position.board.get (!R.side) = R.target.position.board.get (!R.side) := by
  obtain ⟨as, has, hpool⟩ := follow_word_inputs_above_bound hpath side
  have hrun := R.run.append has
  have hinc : (R.labels.marker :: (R.atoms ++ as).map Prod.snd).Pairwise (· < ·) := by
    have hc := ((Position.history_dataInvariant q).2.1 side).2
    rw [LabeledWord.runAtoms_coordinates hrun.run] at hc
    simpa [LabeledCode.rootCursor] using hc
  apply winning_first_root_request hHN hH blue R.target R.targetWinning R.side R.labels
    R.targetPending R.targetInitial R.targetBound hrun.run hm hindex hinc
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  rcases List.mem_append.mp ha with ha | ha
  · exact (R.pool a ha).1
  · exact (hpool a ha).1

theorem request_shared {p : Concrete.Hist N} (side : Bool)
    (R : FirstRootPlan N H blue b σ (p.position.board.get side))
    (hHN : H ⊆ N) (hH : H.Infinite)
    (hwin : (exactGame N blue).ArchitectWins H b σ p) :
    ∃ lower upper d c,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p lower ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) R.target upper ∧
      lower.position.pending = some ⟨side, .advance d⟩ ∧
      upper.position.pending = some ⟨R.side, .advance c⟩ ∧ 0 < d ∧ 0 < c ∧
      (lower.position.board.get side).markerEvent = true ∧
      (upper.position.board.get R.side).markerEvent = true ∧
      LabeledWord.SameStructure (lower.position.board.get side)
        (upper.position.board.get R.side) ∧
      (lower.position.board.get side).rootLabel = R.labels.lower ∧
      (lower.position.board.get side).bodyLabels.length + 1 = R.labels.shared ∧
      ((lower.position.board.get side).rootLabel.filter
        (fun i => i ≤ (lower.position.board.get side).bodyLabels.length + 1)).card =
          R.criticalRank ∧
      (upper.position.board.get R.side).rootLabel = R.labels.upper ∧
      (upper.position.board.get R.side).NoRootPassed ∧
      upper.position.board.get (!R.side) = R.target.position.board.get (!R.side) := by
  obtain ⟨lower, d, hpath, hp, hd, hm, hi⟩ :=
    winning_reach_body_marker hHN hH blue hwin side R.labels.shared R.not_start R.before_body
  obtain ⟨upper, c, hupper, hu, hc, huword, hum, hufirst, huother⟩ :=
    R.fire_after side hHN hH hpath hm hi
  obtain ⟨as, has, _⟩ := follow_word_inputs_above_bound hpath side
  have hroot : (lower.position.board.get side).rootLabel = R.labels.lower :=
    (has.rootLabel_eq R.not_start).trans R.rootLabel
  refine ⟨lower, upper, d, c, hpath, hupper, hp, hu, hd, hc, hm, hum, ?_,
    hroot, hi, ?_, ?_, hufirst, huother⟩
  · rw [huword]
    exact (LabeledWord.rootRelabel_sameStructure R.labels.upper _).symm
  · rw [hroot, hi]
    exact R.labels.shared_rank
  · simp only [huword, LabeledWord.rootRelabel]

#print axioms fire_after
#print axioms request_shared

end Erdos591.Positive.Game.Relay.FirstRootPlan

end Erdos118.Reused591
