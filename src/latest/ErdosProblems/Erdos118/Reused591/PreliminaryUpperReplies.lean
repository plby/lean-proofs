import ErdosProblems.Erdos118.Reused591.RankedFirstLeafLabels
import ErdosProblems.Erdos118.Reused591.NextLeafReplay
import ErdosProblems.Erdos118.Reused591.DeferredBodyMarker
import ErdosProblems.Erdos118.Reused591.SplicedNextRoot
import ErdosProblems.Erdos118.Reused591.FollowFreshInputs
import ErdosProblems.Erdos118.Reused591.LastBodyEndpoint

namespace Erdos118.Reused591

/-!
# The actual upper U reply after the two nonempty preliminary phases

A nonsingleton upper label replays the old lower maximum as its second
leaf. A singleton instead completes its pending next-body reply across
the retained prefix, imposing the new lower bound only on its new tail.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem preliminary_upper_u_second {N H HD : Set ℕ}
    (hHN : H ⊆ N) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} (σ : (exactGame N blue).ArchitectStrategy)
    (old fine upper : Concrete.Hist N) {B n c s : ℕ}
    (D : RankedFirstLeafLabels HD B n c s) (hc : 2 ≤ c)
    (hp : upper.position.pending = some ⟨true, .advance 0⟩)
    (hshape : LabeledWord.SameStructure upper.position.board.right old.position.board.right)
    (hrel : upper.position.board.right.relaxed = true)
    (hlabel : upper.position.board.right.currentLabel = D.targetView.upper)
    (hindex : upper.position.board.right.leafIndex = D.targetView.pivot)
    (hOldRel : old.position.board.right.relaxed = true)
    (hlabels : fine.position.board.right.bodyLabels = old.position.board.right.bodyLabels)
    (hFineIndex : fine.position.board.right.leafIndex = D.source.sup id)
    {bs : List (Finset ℕ × ℕ)}
    (hrun : LabeledWord.LegalRun old.position.board.right bs fine.position.board.right)
    (hpool : ∀ atom ∈ bs, atom.2 ∈ H ∧ max upper.position.bound (b upper) < atom.2) :
    ∃ q, (exactGame N blue).FollowStep σ H b upper q ∧ q.position.pending = none ∧
      LabeledWord.SameStructure q.position.board.right fine.position.board.right ∧
      q.position.board.right.relaxed = true ∧
      q.position.board.right.rootLabel = upper.position.board.right.rootLabel ∧
      q.position.board.right.bodyLabels = upper.position.board.right.bodyLabels ∧
      q.position.board.right.currentLabel = D.targetView.upper ∧
      q.position.board.right.leafIndex = D.source.sup id ∧
      q.position.board.left = upper.position.board.left ∧
      ∀ x ∈ q.position.board.left.coordinates,
        x ≤ q.position.board.right.coordinates.getLastD 0 := by
  have hup : LabeledWord.UpToLeaf (D.source.sup id) upper.position.board.right :=
    ⟨(of_decide_eq_true hrel).2.1, hlabel ▸ D.last_target hc,
      by simpa only [hindex] using D.pivot_lt_last.le⟩
  have hlt : upper.position.board.right.leafIndex < D.source.sup id := by
    simpa only [hindex] using D.pivot_lt_last
  have hnext : ∀ x ∈ upper.position.board.right.currentLabel,
      upper.position.board.right.leafIndex < x → D.source.sup id ≤ x := by
    intro x hx hgt
    exact D.target_next x (hlabel ▸ hx) (by simpa only [hindex] using hgt)
  have hmarker := hrun.bodyMarker_of_body_length
    (LabeledWord.relaxed_ne_start ((Position.history_dataInvariant old).2.1 true).1 hOldRel)
      (congrArg List.length hlabels)
  have hinc : (bs.map Prod.snd).Pairwise (· < ·) := by
    have hi := ((Position.history_dataInvariant fine).2.1 true).2
    change fine.position.board.right.coordinates.Pairwise (· < ·) at hi
    rw [LabeledWord.runAtoms_coordinates hrun.run] at hi
    exact (List.pairwise_append.mp hi).2.1
  obtain ⟨q, hstep, hnone, hqshape, hqrel, hqlabels, hqother⟩ :=
    Concrete.follow_next_leaf hHN (payoff blue) σ upper true hp hshape hup hlt hnext
      hrun.run hFineIndex (congrArg List.length hlabels) hmarker hinc (by
        intro atom ha
        exact ⟨(hpool atom ha).1, (le_max_left _ _).trans_lt (hpool atom ha).2,
          (le_max_right _ _).trans_lt (hpool atom ha).2⟩)
  simp only [Board.get, Bool.not_true] at hqshape hqrel hqlabels hqother
  obtain ⟨as, has, _⟩ := follow_word_inputs_above_bound (Relation.ReflTransGen.single hstep) true
  have hroot := has.rootLabel_eq (LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant upper).2.1 true).1 hrel)
  refine ⟨q, hstep, hnone, hqshape, hqrel, hroot, hqlabels, ?_,
    hqshape.leaf_eq.trans hFineIndex, hqother, ?_⟩
  · simpa only [LabeledWord.currentLabel, hqlabels] using hlabel
  · simpa only [Board.get, Bool.not_true] using
      (FiniteResponseGame.FollowStep.next (exactGame N blue) hstep).reply_separation hp

theorem preliminary_upper_u_singleton {N H HD HU : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} (σ : (exactGame N blue).ArchitectStrategy)
    (old fine upper : Concrete.Hist N) {B n s BU e g j k : ℕ}
    (D : RankedFirstLeafLabels HD B n 1 s) (U : SplicedRootLabels HU BU e g j k)
    (hp : upper.position.pending = some ⟨true, .advance 0⟩)
    (hshape : LabeledWord.SameStructure upper.position.board.right old.position.board.right)
    (hrel : upper.position.board.right.relaxed = true)
    (hlabel : upper.position.board.right.currentLabel = D.targetView.upper)
    (hindex : upper.position.board.right.leafIndex = D.targetView.pivot)
    (hroot : upper.position.board.right.rootLabel = U.upper)
    (hbody : upper.position.board.right.bodyLabels.length = U.first)
    (hFineBody : fine.position.board.right.bodyLabels.length = U.first)
    {bs : List (Finset ℕ × ℕ)}
    (hrun : LabeledWord.LegalRun old.position.board.right bs fine.position.board.right)
    (hpool : ∀ atom ∈ bs, atom.2 ∈ H ∧ max upper.position.bound (b upper) < atom.2)
    (C : ℕ) :
    ∃ i q, i ∈ U.upper ∧ U.first < i ∧ i ≤ U.anchor ∧
      (∀ x ∈ U.upper, U.first < x → i ≤ x) ∧
      (exactGame N blue).FollowStep σ H b upper q ∧ q.position.pending = none ∧
      q.position.board.right.markerEvent = true ∧
      q.position.board.right.rootLabel = U.upper ∧
      q.position.board.right.bodyLabels.length + 1 = i ∧
      q.position.board.right.bodyLabels.length < U.anchor ∧
      q.position.board.left = upper.position.board.left ∧
      ∃ anchor, LabeledWord.SameStructure fine.position.board.right anchor ∧
        ∃ as, LabeledWord.LegalRun anchor as q.position.board.right ∧
          ∀ atom ∈ as, atom.2 ∈ H ∧ C < atom.2 := by
  obtain ⟨i, hi, hFirstLt, hAnchor, hLeast⟩ := U.next_after_first_le_anchor
  have hno : upper.position.board.right.NoLeafPending := by
    intro x hx
    rw [hlabel, D.target_singleton] at hx
    rw [Finset.mem_singleton.mp hx, hindex]
  have hbefore : LabeledWord.BeforeBody i upper.position.board.right :=
    ⟨hroot ▸ hi, by simpa only [hbody] using hFirstLt⟩
  have hnext : ∀ x ∈ upper.position.board.right.rootLabel,
      upper.position.board.right.bodyLabels.length < x → i ≤ x := by
    simpa only [hroot, hbody] using hLeast
  obtain ⟨q, hstep, hnone, hm, hidx, hother, anchor, hAnchorShape, as, has, hAsPool⟩ :=
    deferred_next_marker_from_body_prefix_or_empty hHN hH blue σ upper true hp hrel hno
      hbefore hnext hshape hrun (by simpa only [hFineBody] using hFirstLt)
      ((Position.history_dataInvariant fine).2.1 true).2 hpool C
  simp only [Board.get, Bool.not_true] at hm hidx hother has
  obtain ⟨cs, hcs, _⟩ := follow_word_inputs_above_bound (Relation.ReflTransGen.single hstep) true
  have hqroot : q.position.board.right.rootLabel = U.upper :=
    (hcs.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant upper).2.1 true).1 hrel)).trans hroot
  exact ⟨i, q, hi, hFirstLt, hAnchor, hLeast, hstep, hnone, hm, hqroot, hidx,
    by omega, hother, anchor, hAnchorShape, as, has, hAsPool⟩

#print axioms preliminary_upper_u_second
#print axioms preliminary_upper_u_singleton

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
