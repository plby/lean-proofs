import ErdosProblems.Erdos591.SelectedSuffixRanks
import ErdosProblems.Erdos591.LocalizedCheckpoint

/-!
# The last upper anchor leaf leaves T at precisely the preceding prescribed rank

The terminal critical suffix loses exactly the anchor body's size.
The actual-history suffix balance and the last T body's rank identity
then identify T's current rank with that size. No alternation premise
or assumed synchronization of the two cursors is used.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem history_anchor_last_rank {N H : Set ℕ} {B e g j k : ℕ}
    (U : SplicedRootLabels H B e g j (k + 1)) {p q : Concrete.Hist N}
    (hpath : Relation.ReflTransGen (fun p q => History.Next q p) p q)
    {s t : G} (hc : Clear q.position.board s t) (hmax : MaxOrder true q.position.board)
    (hl : p.position.board.left.relaxed = true) (hr : p.position.board.right.relaxed = true)
    (horder : p.position.board.left.coordinates.getLastD 0 <
      p.position.board.right.coordinates.getLastD 0)
    (hTlast : p.position.board.left.bodyLabels.length = p.position.board.left.lastSelectedBody)
    (hUbody : p.position.board.right.bodyLabels.length = U.anchor)
    (hUno : p.position.board.right.NoLeafPending)
    (hUroot : q.position.board.right.rootLabel = U.upper)
    (hspec : q.position.board.right.CriticalPairSpec q.position.board.left.lastSelectedLabel.card
      (q.position.board.right.criticalPair q.position.board.left.lastSelectedLabel.card))
    (hcritical : q.position.board.right.criticalBodyRank
      q.position.board.left.lastSelectedLabel.card = k)
    (hlast : criticalLastColor q = true) :
    (p.position.board.left.currentLabel.filter
      (fun x => x ≤ p.position.board.left.leafIndex)).card =
        p.position.board.right.currentLabel.card := by
  have currentData (side : Bool) (hrel : (p.position.board.get side).relaxed = true) :
      0 < (p.position.board.get side).bodyLabels.length ∧
        0 < (p.position.board.get side).leafIndex ∧
        (q.position.board.get side).bodyLabels.getD
          ((p.position.board.get side).bodyLabels.length - 1) ∅ =
            (p.position.board.get side).currentLabel ∧
        (q.position.board.get side).rootLabel = (p.position.board.get side).rootLabel := by
    have hw := ((Position.history_dataInvariant p).2.1 side).1
    have hd := of_decide_eq_true hrel
    have hbodyPos := (hw.2.2.1 _ hd.2.1).1
    have hstart := LabeledWord.relaxed_ne_start hw hrel
    obtain ⟨as, has, _⟩ := (History.reachable_word_extension hpath).2 side
    refine ⟨hbodyPos, hd.1, ?_, has.rootLabel_eq hstart⟩
    rw [has.body_getD_eq hstart (by omega)]
    exact (LabeledWord.currentLabel_eq_getD (by omega)).symm
  obtain ⟨hTpos, hTleafPos, hTlabel, hTroot⟩ := currentData false hl
  obtain ⟨hUpos, hUleafPos, hUlabel, _hUrootOld⟩ := currentData true hr
  simp only [Board.get] at hTpos hTleafPos hTlabel hTroot hUpos hUleafPos hUlabel
  have hTlastQ : p.position.board.left.bodyLabels.length =
      q.position.board.left.lastSelectedBody := by
    simpa only [LabeledWord.lastSelectedBody, hTroot] using hTlast
  have hTmem : p.position.board.left.bodyLabels.length ∈ q.position.board.left.rootLabel :=
    hTroot ▸ (of_decide_eq_true hl).2.1
  have hTleafMem : p.position.board.left.leafIndex ∈
      q.position.board.left.bodyLabels.getD (p.position.board.left.bodyLabels.length - 1) ∅ := by
    rw [hTlabel]
    exact (of_decide_eq_true hl).2.2
  have hTsuffix := LabeledWord.selectedLeafPairsFrom_last_rank hTlastQ hTpos hTleafPos
    hTmem hTleafMem
  have hTcard : q.position.board.left.lastSelectedLabel.card =
      p.position.board.left.currentLabel.card := by
    simp only [LabeledWord.lastSelectedLabel, ← hTlastQ, hTlabel]
  let critical := q.position.board.right.criticalPair q.position.board.left.lastSelectedLabel.card
  have hanchor : U.anchor ∈ q.position.board.right.rootLabel := hUroot ▸ U.anchor_upper
  have hnext := finite_rank_successor q.position.board.right.rootLabel hanchor
    (x := critical.1) (by
      change (q.position.board.right.rootLabel.filter (fun x => x ≤ U.anchor)).card =
        q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card + 1
      rw [hcritical, hUroot, U.anchor_upper_rank])
  have hCriticalLast : ∀ x ∈ q.position.board.right.bodyLabels.getD (critical.1 - 1) ∅,
      x ≤ critical.2 := by
    simpa only [criticalLastColor, LabeledWord.criticalLast, decide_eq_true_eq] using hlast
  have hULeaf : p.position.board.right.leafIndex ∈
      q.position.board.right.bodyLabels.getD (U.anchor - 1) ∅ := by
    rw [← hUbody, hUlabel]
    exact (of_decide_eq_true hr).2.2
  have hULast : ∀ x ∈ q.position.board.right.bodyLabels.getD (U.anchor - 1) ∅,
      x ≤ p.position.board.right.leafIndex := by
    rw [← hUbody, hUlabel]
    exact hUno
  have hUsuffix := LabeledWord.selectedLeafPairsFrom_adjacent_last
    (Finset.mem_sigma.mp hspec.1).1 (Finset.mem_sigma.mp hspec.1).2 hanchor hULeaf
    hspec.2.1 hspec.2.2.1 (hUbody ▸ hUpos) hUleafPos hnext.1 hnext.2 hCriticalLast hULast
  have hcount := hspec.2.2.2
  rw [← hUbody, hUlabel, hcount, hTcard] at hUsuffix
  rw [hTlabel] at hTsuffix
  have hbalance := history_inside_relaxed_suffix_balance hpath hc hmax hl hr horder
  omega

#print axioms history_anchor_last_rank

end Erdos591.Positive.Game.Payoff
