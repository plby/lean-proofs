import ErdosProblems.Erdos591.AlignedRootPlan
import ErdosProblems.Erdos591.PrepareLeafHistory
import ErdosProblems.Erdos591.FollowFreshInputs

/-!
# Preparing the shared penultimate-lower, first-upper selected body

Reach its actual lower marker request, replay the retained upper root,
then choose the last-first body overlap above both newly known bounds.
The saved upper body response remains unsubmitted.
-/

namespace Erdos591.Positive.Game.Relay.AlignedRootPlan

open Erdos591.Negative.Exact
open Payoff

variable {N H : Set ℕ} {blue : SimpleGraph G} {b : Concrete.Hist N → ℕ}
  {σ : (exactGame N blue).ArchitectStrategy}

theorem fire_after {p q : Concrete.Hist N} (side : Bool)
    (R : AlignedRootPlan N H blue b σ (p.position.board.get side))
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
  apply winning_aligned_root_request hHN hH blue R.target R.targetWinning R.side R.labels
    R.targetPending R.targetInitial R.targetBound hrun.run hm hindex hinc
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  rcases List.mem_append.mp ha with ha | ha
  · exact (R.pool a ha).1
  · exact (hpool a ha).1

theorem prepare_shared {p : Concrete.Hist N} (side : Bool)
    (R : AlignedRootPlan N H blue b σ (p.position.board.get side))
    (hHN : H ⊆ N) (hH : H.Infinite)
    (hwin : (exactGame N blue).ArchitectWins H b σ p) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = none ∧ (q.position.board.get side).relaxed = true ∧
      (∀ y ∈ (q.position.board.get (!side)).coordinates,
        y ≤ (q.position.board.get side).coordinates.getLastD 0) ∧
      ∃ P : PreparedLeaf N H blue b σ (q.position.board.get side),
        P.side = R.side ∧
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) R.target P.target ∧
        P.stem.rootLabel = R.labels.lower ∧
        P.stem.bodyLabels.length + 1 = R.labels.shared ∧
        (P.target.position.board.get P.side).rootLabel = R.labels.upper ∧
        (P.target.position.board.get P.side).NoRootPassed ∧
        P.target.position.board.get (!P.side) = R.target.position.board.get (!R.side) := by
  obtain ⟨m, d, hpm, hmp, hd, hm, hmi⟩ := winning_reach_body_marker hHN hH blue hwin
    side R.labels.shared R.not_start R.before_body
  obtain ⟨upper, c, hupper, hu, hc, huword, hum, hufirst, huother⟩ :=
    R.fire_after side hHN hH hpm hm hmi
  let B := max (max m.position.bound (b m)) (max upper.position.bound (b upper))
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B d c hd hc
  have hsame : LabeledWord.SameStructure (m.position.board.get side)
      (upper.position.board.get R.side) := by
    rw [huword]
    exact (LabeledWord.rootRelabel_sameStructure R.labels.upper _).symm
  obtain ⟨q, hmq, hqn, hqr, _hqo, P, hPt, hPs, _hPL, hstem⟩ :=
    prepare_leaf hHN hH blue
      (R.targetWinning.of_reachable (exactGame N blue) hupper) side R.side L
      hmp hu hm hum hsame (le_max_left _ _) (le_max_right _ _)
  obtain ⟨as, has, _⟩ := follow_word_inputs_above_bound hpm side
  have hroot : (m.position.board.get side).rootLabel = R.labels.lower :=
    (has.rootLabel_eq R.not_start).trans R.rootLabel
  refine ⟨q, hpm.tail hmq, hqn, hqr,
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hmq).reply_separation hmp,
    P, hPs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hPt] using hupper
  · simpa only [hstem] using hroot
  · simpa only [hstem] using hmi
  · simp only [hPt, hPs, huword, LabeledWord.rootRelabel]
  · simpa only [hPt, hPs] using hufirst
  · simpa only [hPt, hPs] using huother

#print axioms fire_after
#print axioms prepare_shared

end Erdos591.Positive.Game.Relay.AlignedRootPlan
