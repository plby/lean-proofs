import ErdosProblems.Erdos118.Reused591.CriticalLeafLabels
import ErdosProblems.Erdos118.Reused591.NextLeafReplay
import ErdosProblems.Erdos118.Reused591.LastBodyEndpoint
import ErdosProblems.Erdos118.Reused591.FreshLeafNextMarker

namespace Erdos118.Reused591

/-!
# Replay the first preliminary T run as the saved upper second-leaf reply

The old lower maximum is the second upper selection. Its literal
same-body run satisfies the original upper response bound. Submit it
once, then issue the upper U continuation request before making any
new U coordinate in the following preliminary phase.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem preliminary_upper_second {N H K HD : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (old fine upper : Concrete.Hist N) {B n c s : ℕ}
    (D : CriticalLeafLabels HD B n c s)
    (hwin : (exactGame N blue).ArchitectWins H b σ upper)
    (hp : upper.position.pending = some ⟨false, .advance 0⟩)
    (hshape : LabeledWord.SameStructure upper.position.board.left old.position.board.right)
    (hrel : upper.position.board.left.relaxed = true)
    (hlabel : upper.position.board.left.currentLabel = D.upperView.upper)
    (hindex : upper.position.board.left.leafIndex = D.upperView.pivot)
    (hOldRel : old.position.board.right.relaxed = true)
    (hlabels : fine.position.board.right.bodyLabels = old.position.board.right.bodyLabels)
    (hFineIndex : fine.position.board.right.leafIndex = D.lower.sup id)
    (hUrel : upper.position.board.right.relaxed = true)
    (hUpending : Macro.Pending upper.position.board.right)
    {bs : List (Finset ℕ × ℕ)}
    (hrun : LabeledWord.LegalRun old.position.board.right bs fine.position.board.right)
    (hpool : ∀ atom ∈ bs, atom.2 ∈ K ∧ max upper.position.bound (b upper) < atom.2) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upper q ∧
      q.position.pending = some ⟨true, .advance 0⟩ ∧
      LabeledWord.SameStructure q.position.board.left fine.position.board.right ∧
      q.position.board.left.relaxed = true ∧
      q.position.board.left.bodyLabels = upper.position.board.left.bodyLabels ∧
      q.position.board.left.currentLabel = D.upperView.upper ∧
      q.position.board.left.leafIndex = D.lower.sup id ∧
      q.position.board.right = upper.position.board.right ∧
      ∀ x ∈ q.position.board.right.coordinates,
        x ≤ q.position.board.left.coordinates.getLastD 0 := by
  have hup : LabeledWord.UpToLeaf (D.lower.sup id) upper.position.board.left :=
    ⟨(of_decide_eq_true hrel).2.1, hlabel ▸ D.last_upper,
      by simpa only [hindex] using D.pivot_lt_last.le⟩
  have hlt : upper.position.board.left.leafIndex < D.lower.sup id := by
    simpa only [hindex] using D.pivot_lt_last
  have hnext : ∀ x ∈ upper.position.board.left.currentLabel,
      upper.position.board.left.leafIndex < x → D.lower.sup id ≤ x := by
    intro x hx hgt
    exact D.upper_next x (hlabel ▸ hx) (by simpa only [hindex] using hgt)
  have hmarker := hrun.bodyMarker_of_body_length
    (LabeledWord.relaxed_ne_start ((Position.history_dataInvariant old).2.1 true).1 hOldRel)
      (congrArg List.length hlabels)
  have hinc : (bs.map Prod.snd).Pairwise (· < ·) := by
    have hi := ((Position.history_dataInvariant fine).2.1 true).2
    change fine.position.board.right.coordinates.Pairwise (· < ·) at hi
    rw [LabeledWord.runAtoms_coordinates hrun.run] at hi
    exact (List.pairwise_append.mp hi).2.1
  obtain ⟨v, huv, _hvn, hvshape, hvrel, hvlabels, hvother⟩ :=
    Concrete.follow_next_leaf hHN (payoff blue) σ upper false hp hshape hup hlt hnext
      hrun.run hFineIndex (congrArg List.length hlabels) hmarker hinc (by
        intro atom ha
        exact ⟨hKH (hpool atom ha).1, (le_max_left _ _).trans_lt (hpool atom ha).2,
          (le_max_right _ _).trans_lt (hpool atom ha).2⟩)
  simp only [Board.get, Bool.not_false] at hvshape hvrel hvlabels hvother
  have hvsep := (FiniteResponseGame.FollowStep.next (exactGame N blue) huv).reply_separation hp
  obtain ⟨q, hvq, hqBoard, hqp⟩ := winning_next_selection_after_fresh_leaf hHN hH blue
    (hwin.of_reachable (exactGame N blue) (.single huv)) false hvrel hvsep
    (by simpa only [Board.get, Bool.not_false, hvother] using hUrel)
    (by simpa only [Board.get, Bool.not_false, hvother] using hUpending)
  refine ⟨q, (Relation.ReflTransGen.single huv).trans hvq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Bool.not_false] using hqp
  · simpa only [hqBoard] using hvshape
  · simpa only [hqBoard] using hvrel
  · simpa only [hqBoard] using hvlabels
  · simpa only [hqBoard, LabeledWord.currentLabel, hvlabels] using hlabel
  · simpa only [hqBoard] using hvshape.leaf_eq.trans hFineIndex
  · simpa only [hqBoard] using hvother
  · simpa only [hqBoard, Board.get, Bool.not_false] using hvsep

#print axioms preliminary_upper_second

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
