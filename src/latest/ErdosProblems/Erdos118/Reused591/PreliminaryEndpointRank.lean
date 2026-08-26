import ErdosProblems.Erdos118.Reused591.SameBodySuffixRanks
import ErdosProblems.Erdos118.Reused591.CriticalCheckpoint

namespace Erdos118.Reused591

/-!
# Exhausting the old critical body fixes the exact preliminary S rank

At a fresh opposite endpoint in the same body as the old critical
checkpoint, its suffix has decreased by exactly the consumed leaf
rank. If that body is exhausted and S is in its last selected body,
the inside suffix balance identifies S's current rank with the old
critical-body remainder. This is the endpoint count for E_T and E_U.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem history_preliminary_last_rank {N : Set ℕ} {old p q : Concrete.Hist N}
    (holdp : Relation.ReflTransGen (fun p q => History.Next q p) old p)
    (hpath : Relation.ReflTransGen (fun p q => History.Next q p) p q)
    (hOld : CriticalCheckpoint old)
    {s t : G} (hc : Clear q.position.board s t) (hmax : MaxOrder true q.position.board)
    (hl : p.position.board.left.relaxed = true) (hr : p.position.board.right.relaxed = true)
    (horder : p.position.board.left.coordinates.getLastD 0 <
      p.position.board.right.coordinates.getLastD 0)
    (hSlast : p.position.board.left.bodyLabels.length = p.position.board.left.lastSelectedBody)
    (hTbody : p.position.board.right.bodyLabels = old.position.board.right.bodyLabels)
    (hTno : p.position.board.right.NoLeafPending)
    (hspec : q.position.board.right.CriticalPairSpec q.position.board.left.lastSelectedLabel.card
      (q.position.board.right.criticalPair q.position.board.left.lastSelectedLabel.card)) :
    (p.position.board.left.currentLabel.filter
      (fun x => x ≤ p.position.board.left.leafIndex)).card =
        old.position.board.right.currentLabel.card -
          (old.position.board.right.currentLabel.filter
            (fun x => x ≤ old.position.board.right.leafIndex)).card := by
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
  obtain ⟨hSpos, hSleafPos, hSlabel, hSroot⟩ := currentData false hl
  obtain ⟨hTpos, hTleafPos, hTlabel, hTroot⟩ := currentData true hr
  simp only [Board.get] at hSpos hSleafPos hSlabel hSroot hTpos hTleafPos hTlabel hTroot
  have hSlastQ : p.position.board.left.bodyLabels.length =
      q.position.board.left.lastSelectedBody := by
    simpa only [LabeledWord.lastSelectedBody, hSroot] using hSlast
  have hSmem : p.position.board.left.bodyLabels.length ∈ q.position.board.left.rootLabel :=
    hSroot ▸ (of_decide_eq_true hl).2.1
  have hSleafMem : p.position.board.left.leafIndex ∈
      q.position.board.left.bodyLabels.getD (p.position.board.left.bodyLabels.length - 1) ∅ := by
    rw [hSlabel]
    exact (of_decide_eq_true hl).2.2
  have hSsuffix := LabeledWord.selectedLeafPairsFrom_last_rank hSlastQ hSpos hSleafPos
    hSmem hSleafMem
  have hScard : q.position.board.left.lastSelectedLabel.card =
      p.position.board.left.currentLabel.card := by
    simp only [LabeledWord.lastSelectedLabel, ← hSlastQ, hSlabel]
  have hTcurrent : p.position.board.right.currentLabel =
      old.position.board.right.currentLabel := by
    simp only [LabeledWord.currentLabel, hTbody]
  have hTlength := congrArg List.length hTbody
  have hTmem : p.position.board.right.bodyLabels.length ∈ q.position.board.right.rootLabel :=
    hTroot ▸ (of_decide_eq_true hr).2.1
  have hTleafMem : p.position.board.right.leafIndex ∈
      q.position.board.right.bodyLabels.getD (p.position.board.right.bodyLabels.length - 1) ∅ := by
    rw [hTlabel]
    exact (of_decide_eq_true hr).2.2
  have hOldLeafMem : old.position.board.right.leafIndex ∈
      q.position.board.right.bodyLabels.getD (p.position.board.right.bodyLabels.length - 1) ∅ := by
    rw [hTlabel, hTcurrent]
    exact (of_decide_eq_true hOld.right_relaxed).2.2
  have hTranks := LabeledWord.selectedLeafPairsFrom_same_body_rank hTmem hOldLeafMem hTleafMem
    hTpos (of_decide_eq_true hOld.right_relaxed).1 hTleafPos
  have hTall : (p.position.board.right.currentLabel.filter
      (fun x => x ≤ p.position.board.right.leafIndex)) = p.position.board.right.currentLabel :=
    Finset.filter_eq_self.mpr hTno
  rw [hTlabel, hTall, hTcurrent] at hTranks
  have hpair := (history_critical_observables (holdp.trans hpath) hc hmax
    hOld.left_relaxed hOld.right_relaxed hOld.coordinate_order hOld.left_before
      hOld.left_penultimate hOld.left_exhausted).1
  have hcount := hspec.2.2.2
  rw [hpair, ← hTlength, hScard] at hcount
  change (q.position.board.right.selectedLeafPairsFrom
    (p.position.board.right.bodyLabels.length - 1)
      (old.position.board.right.leafIndex - 1)).card =
        p.position.board.left.currentLabel.card at hcount
  rw [hSlabel] at hSsuffix
  have hbalance := history_inside_relaxed_suffix_balance hpath hc hmax hl hr horder
  omega

#print axioms history_preliminary_last_rank

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
