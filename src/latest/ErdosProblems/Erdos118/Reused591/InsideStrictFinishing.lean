import ErdosProblems.Erdos118.Reused591.InsideStrictNextLeafEndgame
import ErdosProblems.Erdos118.Reused591.InsideStrictNextBodyEndgame
import ErdosProblems.Erdos118.Reused591.InsideStrictExhaustedEndgame

namespace Erdos118.Reused591

/-! # All cases of the strict finishing configuration -/

namespace Erdos591.Positive.Game

theorem LabeledWord.NoLeafPending.next_body_or_exhausted {w : LabeledWord}
    (hno : w.NoLeafPending) :
    (∃ i, LabeledWord.BeforeBody i w ∧
      ∀ k ∈ w.rootLabel, w.bodyLabels.length < k → i ≤ k) ∨ ¬ Macro.Pending w := by
  classical
  let F := w.rootLabel.filter (fun k => w.bodyLabels.length < k)
  by_cases hF : F.Nonempty
  · left
    let i := F.min' hF
    have hi : i ∈ F := Finset.min'_mem F hF
    refine ⟨i, ⟨(Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩, ?_⟩
    exact fun k hk hlt => Finset.min'_le F k (Finset.mem_filter.mpr ⟨hk, hlt⟩)
  · right
    rintro (⟨i, hi, hlt⟩ | ⟨_, i, hi, hlt⟩)
    · exact hF ⟨i, Finset.mem_filter.mpr ⟨hi, hlt⟩⟩
    · exact not_lt_of_ge (hno i hi) hlt

namespace Payoff

open Erdos591.Negative.Exact

theorem inside_strict_finishing {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (oldST su oldTU : Concrete.Hist N)
    (hwinST : (exactGame N blue).ArchitectWins H b σ oldST)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hwinTU : (exactGame N blue).ArchitectWins H b σ oldTU)
    (hmSU : su.position.mode = some true) (hmTU : oldTU.position.mode = some true)
    (hpST : oldST.position.pending = some ⟨false, .advance 0⟩)
    (hpTU : oldTU.position.pending = some ⟨true, .advance 0⟩)
    (hSl : su.position.board.left.relaxed = true)
    (hUr : su.position.board.right.relaxed = true)
    (hsep : ∀ x ∈ su.position.board.left.coordinates,
      x ≤ su.position.board.right.coordinates.getLastD 0)
    (hS : LabeledWord.SameStructure oldST.position.board.left su.position.board.left)
    (hT : LabeledWord.SameStructure oldST.position.board.right oldTU.position.board.left)
    (hU : LabeledWord.SameStructure oldTU.position.board.right su.position.board.right)
    {gamma : ℕ} (hSUp : LabeledWord.UpToLeaf gamma oldST.position.board.left)
    (hSstrict : oldST.position.board.left.leafIndex < gamma)
    (hSnext : ∀ j ∈ oldST.position.board.left.currentLabel,
      oldST.position.board.left.leafIndex < j → gamma ≤ j)
    (hSroot : ∀ i ∈ su.position.board.left.rootLabel,
      i ≤ su.position.board.left.bodyLabels.length)
    (hgamma : gamma ∈ su.position.board.left.currentLabel)
    (hSlast : ∀ j ∈ su.position.board.left.currentLabel, j ≤ gamma)
    (hTrel : oldST.position.board.right.relaxed = true)
    {lastT : ℕ} (hUpperT : LabeledWord.UpToLeaf lastT oldTU.position.board.left)
    (hUpperStrict : oldTU.position.board.left.leafIndex < lastT)
    (hTroot : ∀ i ∈ oldTU.position.board.left.rootLabel,
      i ≤ oldTU.position.board.left.bodyLabels.length)
    (hTlast : ∀ j ∈ oldTU.position.board.left.currentLabel, j ≤ lastT)
    (hLowerT :
      (LabeledWord.UpToLeaf lastT oldST.position.board.right ∧
        ∀ j ∈ oldST.position.board.right.currentLabel,
          oldST.position.board.right.leafIndex < j → lastT ≤ j) ∨
      oldST.position.board.right.NoLeafPending)
    (hUpperUrel : oldTU.position.board.right.relaxed = true)
    (hUpperUno : oldTU.position.board.right.NoLeafPending) {nextU : ℕ}
    (hUpperBefore : LabeledWord.BeforeBody nextU oldTU.position.board.right)
    (hUpperNext : ∀ i ∈ oldTU.position.board.right.rootLabel,
      oldTU.position.board.right.bodyLabels.length < i → nextU ≤ i)
    (hLowerBefore : ∀ i ∈ su.position.board.right.rootLabel, i < nextU) :
    ¬ blue.CliqueFree 3 := by
  rcases hLowerT with ⟨hTUp, hTnext⟩ | hTno
  · have hTstrict : oldST.position.board.right.leafIndex < lastT :=
      hT.leaf_eq.symm ▸ hUpperStrict
    exact inside_strict_next_leaf_endgame hHN hH blue oldST su oldTU hwinST hwinSU hwinTU
      hmSU hmTU hpST hpTU hSl hUr hsep hS hT hU hSUp hSstrict hSnext hSroot hgamma hSlast
      hTUp hTstrict hTnext hUpperT hTroot hTlast
      hUpperUrel hUpperUno hUpperBefore hUpperNext hLowerBefore
  · rcases hTno.next_body_or_exhausted with ⟨nextT, hTbefore, hTnext⟩ | hTlastLower
    · exact inside_strict_next_body_endgame hHN hH blue oldST su oldTU hwinST hwinSU hwinTU
        hmSU hmTU hpST hpTU hSl hUr hsep hS hT hU hSUp hSstrict hSnext hSroot hgamma hSlast
        hTrel hTno hTbefore hTnext hUpperT hUpperStrict hTroot hTlast
        hUpperUrel hUpperUno hUpperBefore hUpperNext hLowerBefore
    · exact inside_strict_exhausted_endgame hHN hH blue oldST su oldTU hwinST hwinSU hwinTU
        hmSU hmTU hpST hpTU hSl hUr hsep hS hT hU hSUp hSstrict hSnext hSroot hgamma hSlast
        hTrel hTlastLower hUpperT hUpperStrict hTroot hTlast
        hUpperUrel hUpperUno hUpperBefore hUpperNext hLowerBefore

#print axioms LabeledWord.NoLeafPending.next_body_or_exhausted
#print axioms inside_strict_finishing

end Payoff

end Erdos591.Positive.Game

end Erdos118.Reused591
