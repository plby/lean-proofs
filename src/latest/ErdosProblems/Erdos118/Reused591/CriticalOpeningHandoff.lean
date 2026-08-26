import ErdosProblems.Erdos118.Reused591.CriticalCheckpoint
import ErdosProblems.Erdos118.Reused591.PreparedSelection
import ErdosProblems.Erdos118.Reused591.NextMarkerReplayHistory

namespace Erdos118.Reused591

/-! # Release the saved upper first leaf while leaving the lower last-marker reply pending -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem CriticalCheckpoint.of_board_eq {N : Set ℕ} {p q : Concrete.Hist N}
    (h : CriticalCheckpoint p) (heq : q.position.board = p.position.board) :
    CriticalCheckpoint q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [heq] using h.left_relaxed
  · simpa only [heq] using h.right_relaxed
  · simpa only [heq] using h.coordinate_order
  · simpa only [heq] using h.left_before
  · simpa only [heq] using h.left_penultimate
  · simpa only [heq] using h.left_exhausted

theorem CriticalCheckpoint.separation {N : Set ℕ} {p : Concrete.Hist N}
    (h : CriticalCheckpoint p) : ∀ x ∈ p.position.board.left.coordinates,
      x ≤ p.position.board.right.coordinates.getLastD 0 := by
  intro x hx
  have hinc := ((Position.history_dataInvariant p).2.1 false).2
  change p.position.board.left.coordinates.Pairwise (· < ·) at hinc
  have hle : x ≤ p.position.board.left.coordinates.getLastD 0 := by
    simpa only [List.getLastD_eq_getLast?,
      List.getLast?_eq_some_getLast (List.ne_nil_of_mem hx), Option.getD_some] using
      (hinc.imp Nat.le_of_lt).rel_getLast hx
  exact hle.trans h.coordinate_order.le

theorem critical_opening_handoff {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (q : Concrete.Hist N)
    (P : PreparedSelection N H blue b σ q.position.board.right)
    (hwin : (exactGame N blue).ArchitectWins H b σ q)
    (hcp : CriticalCheckpoint q) (hselected : q.position.board.right.leafIndex = P.labels.pivot) :
    ∃ old upper, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) q old ∧
      (exactGame N blue).FollowStep σ H b P.target upper ∧
      old.position.board = q.position.board ∧
      old.position.pending = some ⟨false, .advance 0⟩ ∧ CriticalCheckpoint old ∧
      upper.position.pending = none ∧
      LabeledWord.SameStructure old.position.board.right (upper.position.board.get P.side) ∧
      (upper.position.board.get P.side).relaxed = true ∧
      (upper.position.board.get P.side).rootLabel = (P.target.position.board.get P.side).rootLabel ∧
      (upper.position.board.get P.side).currentLabel = P.labels.upper ∧
      (upper.position.board.get P.side).leafIndex = P.labels.pivot ∧
      upper.position.board.get (!P.side) = P.target.position.board.get (!P.side) := by
  have hlastmem : q.position.board.left.lastSelectedBody ∈ q.position.board.left.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id)
      ⟨q.position.board.left.bodyLabels.length, (of_decide_eq_true hcp.left_relaxed).2.1⟩
  have hbefore : LabeledWord.BeforeBody q.position.board.left.lastSelectedBody
      q.position.board.left := ⟨hlastmem, hcp.left_before⟩
  have hlive := hbefore.not_terminal ((Position.history_dataInvariant q).2.1 false).1
  obtain ⟨old, r, hqold, hOldBoard, hpOld⟩ :=
    request_on_live_board (H := H) σ q (Board.not_done_of_live (side := false) hlive)
  have hwinOld := hwin.of_reachable (exactGame N blue) hqold
  have hside : r.side = false := winning_pending_switch hHN hH blue hwinOld hpOld true
    (by simpa only [hOldBoard, Board.get] using hcp.right_relaxed)
    (by simpa only [hOldBoard, Board.get, Bool.not_true] using hcp.separation)
  have hzero := winning_pending_root_advance_zero hHN hH blue hwinOld hpOld false hside
    (by simpa only [hOldBoard, Board.get] using hcp.left_relaxed)
    (by simpa only [hOldBoard, Board.get] using hbefore)
  have hpend : old.position.pending = some ⟨false, .advance 0⟩ := by
    simpa only [hzero] using hpOld
  obtain ⟨upper, huStep, huNone, huCoords, huRel, huOther, huRoot, huBody, huLeaf⟩ :=
    P.fire_full hHN ((Position.history_dataInvariant q).2.1 true).2 hselected
  have hshape : LabeledWord.SameStructure old.position.board.right
      (upper.position.board.get P.side) := by
    obtain ⟨as, has⟩ := History.word_run old true
    obtain ⟨bs, hbs⟩ := History.word_run upper P.side
    apply LabeledWord.sameStructure_of_initial_runs has.run hbs.run
    simpa only [hOldBoard, Board.get] using huCoords.symm
  have huLabel : (upper.position.board.get P.side).currentLabel = P.labels.upper := by
    simp [LabeledWord.currentLabel, huBody]
  exact ⟨old, upper, hqold, huStep, hOldBoard, hpend, hcp.of_board_eq hOldBoard,
    huNone, hshape, huRel, huRoot, huLabel, huLeaf, huOther⟩

#print axioms CriticalCheckpoint.of_board_eq
#print axioms critical_opening_handoff

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
