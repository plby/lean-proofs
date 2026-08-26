import ErdosProblems.Erdos118.Reused591.NextMarkerReplay
import ErdosProblems.Erdos118.Reused591.RootGluingHistory
import ErdosProblems.Erdos118.Reused591.FollowFreshInputs

namespace Erdos118.Reused591

/-! # Submit an older next-body reply at an already reached fine marker -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem next_marker_request_at_endpoint {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (old fine : Concrete.Hist N) (side targetSide : Bool) {i : ℕ}
    (hwin : (exactGame N blue).ArchitectWins H b σ old)
    (hp : old.position.pending = some ⟨side, .advance 0⟩)
    (hrel : (old.position.board.get side).relaxed = true)
    (hno : (old.position.board.get side).NoLeafPending)
    (hbefore : LabeledWord.BeforeBody i (old.position.board.get side))
    (hnext : ∀ x ∈ (old.position.board.get side).rootLabel,
      (old.position.board.get side).bodyLabels.length < x → i ≤ x)
    {anchor : LabeledWord} {as : List (Finset ℕ × ℕ)}
    (hshape : LabeledWord.SameStructure (old.position.board.get side) anchor)
    (hrun : LabeledWord.LegalRun anchor as (fine.position.board.get targetSide))
    (hpool : ∀ a ∈ as, a.2 ∈ H ∧ max old.position.bound (b old) < a.2)
    (hm : (fine.position.board.get targetSide).markerEvent = true)
    (hi : (fine.position.board.get targetSide).bodyLabels.length + 1 = i) :
    ∃ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old q ∧
      q.position.pending = some ⟨side, .advance d⟩ ∧ 0 < d ∧
      LabeledWord.SameStructure (q.position.board.get side)
        (fine.position.board.get targetSide) ∧
      (q.position.board.get side).markerEvent = true ∧
      (q.position.board.get side).bodyLabels.length + 1 = i ∧
      (q.position.board.get side).rootLabel = (old.position.board.get side).rootLabel ∧
      q.position.board.get (!side) = old.position.board.get (!side) := by
  have hinc : (as.map Prod.snd).Pairwise (· < ·) := by
    have hf := ((Position.history_dataInvariant fine).2.1 targetSide).2
    rw [LabeledWord.runAtoms_coordinates hrun.run] at hf
    exact (List.pairwise_append.mp hf).2.1
  obtain ⟨v, hstep, hvn, hvs, hvm, hvi, hvo⟩ :=
    Concrete.follow_next_marker hHN (payoff blue) σ old side hp hshape hrel hno hbefore hnext
      hrun.run hm hi hinc (by
        intro a ha
        exact ⟨(hpool a ha).1, (le_max_left _ _).trans_lt (hpool a ha).2,
          (le_max_right _ _).trans_lt (hpool a ha).2⟩)
  obtain ⟨q, d, hvq, hboard, hpq, hd⟩ := winning_request_at_marker hHN hH blue
    (hwin.of_reachable (exactGame N blue) (.single hstep)) side hvn hvm
  have hpath := (Relation.ReflTransGen.single hstep).tail hvq
  obtain ⟨bs, hbs, _⟩ := follow_word_inputs_above_bound hpath side
  have hroot := hbs.rootLabel_eq (LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant old).2.1 side).1 hrel)
  exact ⟨q, d, hpath, hpq, hd, by simpa only [hboard] using hvs,
    by simpa only [hboard] using hvm, by simpa only [hboard] using hvi,
    hroot, by simpa only [hboard] using hvo⟩

#print axioms next_marker_request_at_endpoint

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
