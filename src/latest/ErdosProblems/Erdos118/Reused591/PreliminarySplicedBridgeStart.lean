import ErdosProblems.Erdos118.Reused591.PreliminaryUpperReplies

namespace Erdos118.Reused591

/-!
# Both actual upper U replies with a separately bounded future bridge pool

The whole old reply stays on J. Only its post-preliminary tail is
required to belong to H = J \ Iic C. For a nonsingleton current
label the whole reply ends at the lower endpoint, so that tail is empty.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem preliminary_spliced_bridge_start {N J HD HU : Set ℕ}
    (hJN : J ⊆ N) (hJ : J.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} (σ : (exactGame N blue).ArchitectStrategy)
    (old fine upper : Concrete.Hist N) {B n c s BU e g j k : ℕ}
    (D : RankedFirstLeafLabels HD B n c s) (U : SplicedRootLabels HU BU e g j k)
    (hc : 0 < c) (hp : upper.position.pending = some ⟨true, .advance 0⟩)
    (hshape : LabeledWord.SameStructure upper.position.board.right old.position.board.right)
    (hrel : upper.position.board.right.relaxed = true)
    (hlabel : upper.position.board.right.currentLabel = D.targetView.upper)
    (hindex : upper.position.board.right.leafIndex = D.targetView.pivot)
    (hroot : upper.position.board.right.rootLabel = U.upper)
    (hbody : upper.position.board.right.bodyLabels.length = U.first)
    (hFineBody : fine.position.board.right.bodyLabels.length = U.first)
    (hOldRel : old.position.board.right.relaxed = true)
    (hlabels : fine.position.board.right.bodyLabels = old.position.board.right.bodyLabels)
    (hFineIndex : fine.position.board.right.leafIndex = D.source.sup id)
    {bs : List (Finset ℕ × ℕ)}
    (hrun : LabeledWord.LegalRun old.position.board.right bs fine.position.board.right)
    (hpool : ∀ atom ∈ bs, atom.2 ∈ J ∧ max upper.position.bound (b upper) < atom.2)
    (C : ℕ) :
    ∃ H, H ⊆ J ∧ H.Infinite ∧ (∀ x ∈ H, C < x) ∧ ∃ p,
      (exactGame N blue).FollowStep σ J b upper p ∧ p.position.pending = none ∧
      p.position.board.left = upper.position.board.left ∧
      p.position.board.right.rootLabel = U.upper ∧
      ((p.position.board.right.relaxed = true ∧
        p.position.board.right.bodyLabels.length < U.anchor ∧
        ∀ x ∈ p.position.board.left.coordinates,
          x ≤ p.position.board.right.coordinates.getLastD 0) ∨
        (p.position.board.right.markerEvent = true ∧
          p.position.board.right.bodyLabels.length + 1 ≤ U.anchor)) ∧
      ∃ anchor, LabeledWord.SameStructure fine.position.board.right anchor ∧
        ∃ as, LabeledWord.LegalRun anchor as p.position.board.right ∧
          ∀ atom ∈ as, atom.2 ∈ H ∧ C < atom.2 := by
  let H := J \ Set.Iic C
  have hHJ : H ⊆ J := fun _ hx => hx.1
  have hH : H.Infinite := hJ.sdiff (Set.finite_Iic C)
  have hFresh : ∀ x ∈ H, C < x := fun _ hx => lt_of_not_ge hx.2
  refine ⟨H, hHJ, hH, hFresh, ?_⟩
  by_cases hcOne : c = 1
  · subst c
    obtain ⟨i, p, _hi, _hFirstLt, hiAnchor, _hLeast, hstep, hnone, hm,
        hUroot, hUindex, _hBefore, hother, anchor, hAnchorShape, as, has, hAsPool⟩ :=
      preliminary_upper_u_singleton hJN hJ blue σ old fine upper D U hp hshape hrel
        hlabel hindex hroot hbody hFineBody hrun hpool C
    refine ⟨p, hstep, hnone, hother, hUroot,
      Or.inr ⟨hm, by simpa only [hUindex] using hiAnchor⟩, anchor, hAnchorShape, as, has, ?_⟩
    intro atom ha
    exact ⟨⟨(hAsPool atom ha).1, not_le_of_gt (hAsPool atom ha).2⟩, (hAsPool atom ha).2⟩
  · obtain ⟨p, hstep, hnone, hFineShape, hUrel, hUroot, hUlabels, _hUlabel,
        _hUindex, hother, hsep⟩ := preliminary_upper_u_second hJN blue σ old fine upper D
      (by omega) hp hshape hrel hlabel hindex hOldRel hlabels hFineIndex hrun hpool
    refine ⟨p, hstep, hnone, hother, hUroot.trans hroot,
      Or.inl ⟨hUrel, ?_, hsep⟩, p.position.board.right, hFineShape.symm, [], .nil _, ?_⟩
    · simpa only [hUlabels, hbody] using U.first_lt_anchor
    · simp only [List.not_mem_nil, false_implies, implies_true]

#print axioms preliminary_spliced_bridge_start

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
