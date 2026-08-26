import ErdosProblems.Erdos591.PreparedBody
import ErdosProblems.Erdos591.DeferredLabels

/-!
# Firing an unsubmitted upper body response at a nonlast lower leaf

The saved prepared record already reserves every candidate label. At
the observed lower leaf, select its candidate and replay the retained
same-body prefix as a single actual upper response. Only the still
pending upper label is chosen; the lower history remains untouched.
-/

namespace Erdos591.Positive.Game.Relay.PreparedBody

open Erdos591.Negative.Exact
open Payoff

variable {N H : Set ℕ} {blue : SimpleGraph G} {b : Concrete.Hist N → ℕ}
  {σ : (exactGame N blue).ArchitectStrategy} {w : LabeledWord}

theorem fire_deferred (P : PreparedBody N H blue b σ w) (hHN : H ⊆ N)
    (hinc : w.coordinates.Pairwise (· < ·)) (hrel : w.relaxed = true)
    (hbefore : w.leafIndex < P.labels.pivot) :
    ∃ q, (exactGame N blue).FollowStep σ H b P.target q ∧ q.position.pending = none ∧
      (q.position.board.get P.side).coordinates = w.coordinates ∧
      (q.position.board.get P.side).relaxed = true ∧
      (q.position.board.get P.side).leafIndex = w.leafIndex ∧
      (q.position.board.get P.side).currentLabel = P.labels.deferredUpper w.leafIndex ∧
      (q.position.board.get P.side).bodyMarker = P.labels.marker ∧
      q.position.board.get (!P.side) = P.target.position.board.get (!P.side) ∧
      (q.position.board.get P.side).rootLabel = (P.target.position.board.get P.side).rootLabel ∧
      (q.position.board.get P.side).bodyLabels.length =
        (P.target.position.board.get P.side).bodyLabels.length + 1 := by
  have hj : w.leafIndex ∈ P.labels.lower := by
    rw [← P.currentLabel]
    exact (of_decide_eq_true hrel).2.2
  let U := P.labels.deferredFirst w.leafIndex hj hbefore
  let xs := P.atoms.map Prod.snd
  have hcount := P.run.leafIndex_of_body_length
    (LabeledWord.read_parser_ne_start P.firstRead) (congrArg List.length P.bodyLabels_eq)
  have hlength : xs.length = w.leafIndex := by
    simpa only [xs, P.first_leaf, Nat.zero_add, List.length_map] using hcount.symm
  have hcoords : w.coordinates = P.stem.coordinates ++ P.labels.marker :: xs := by
    rw [LabeledWord.runAtoms_coordinates P.run.run, (LabeledWord.read_spec P.firstRead).2]
    simp [xs, List.append_assoc]
  have htailInc : (P.labels.marker :: xs).Pairwise (· < ·) := by
    rw [hcoords] at hinc
    exact (List.pairwise_append.mp hinc).2.1
  have hxsPool : ∀ x ∈ xs, x ∈ H := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact (P.pool a ha).1
  have hparser : (P.target.position.board.get P.side).parser =
      .blocks (P.remainingBodies + 1) := P.stemSame.parser_eq.symm.trans P.stemParser
  obtain ⟨u, hr, _hsort, huH, huB⟩ := U.leaf_reply P.target.position.board P.side
    P.remainingBodies xs ((Position.history_dataInvariant P.target).2.1 P.side).1
    hparser P.targetMarker hlength htailInc hxsPool
  obtain ⟨q, hstep, hboard, hnone⟩ := Concrete.follow_reply hHN (payoff blue) σ P.target
    P.targetPending hr huH (fun x hx =>
      ⟨((le_max_left _ _).trans P.targetBound).trans_lt (huB x hx),
        ((le_max_right _ _).trans P.targetBound).trans_lt (huB x hx)⟩)
  have hword : q.position.board.get P.side =
      LabeledWord.bodyLeafCursor (P.target.position.board.get P.side)
        U.upper P.labels.marker P.remainingBodies xs := by
    simp [hboard, U, LastFirstLabels.deferredFirst]
  have hsame : (q.position.board.get P.side).coordinates = w.coordinates := by
    rw [hword, hcoords]
    simp [LabeledWord.bodyLeafCursor, P.stemSame.coordinates_eq]
  have hrelUpper : (q.position.board.get P.side).relaxed = true := by
    rw [hword]
    simpa [LabeledWord.relaxed, LabeledWord.bodyLeafCursor, LabeledWord.currentLabel, hlength] using
      (show 0 < w.leafIndex ∧ (P.target.position.board.get P.side).bodyLabels.length + 1 ∈
          (P.target.position.board.get P.side).rootLabel ∧ w.leafIndex ∈ U.upper from
        ⟨(of_decide_eq_true hrel).1, LabeledWord.marker_body_mem P.targetMarker,
          U.pivot_upper⟩)
  refine ⟨q, hstep, hnone, hsame, hrelUpper, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hword, LabeledWord.bodyLeafCursor, hlength]
  · simp [hword, LabeledWord.bodyLeafCursor, LabeledWord.currentLabel, U,
      LastFirstLabels.deferredFirst]
  · simp [hword, LabeledWord.bodyLeafCursor]
  · simpa [hboard] using hr.other_eq
  · simp [hword, LabeledWord.bodyLeafCursor]
  · simp [hword, LabeledWord.bodyLeafCursor]

#print axioms fire_deferred

end Erdos591.Positive.Game.Relay.PreparedBody
