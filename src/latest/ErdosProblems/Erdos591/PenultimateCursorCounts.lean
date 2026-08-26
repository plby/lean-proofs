import ErdosProblems.Erdos591.SelectedPairEndpoints
import ErdosProblems.Erdos591.CutPersistence
import ErdosProblems.Erdos591.NextMarkerAcceptance

/-!
# Penultimate selected-leaf endpoint counts for a partial cursor

Already read root and body labels are preserved by a legal continuation.
Consequently the finite suffix-cardinality test recovers exactly the
current cursor's exhausted penultimate selected body.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem ClearSide.relaxed_penultimate_iff_suffix_card
    {v last : LabeledWord} {s t : G} {xs ys : List (Finset ℕ × ℕ)}
    (h : ClearSide last s t)
    (hinit : LabeledWord.LegalRun LabeledWord.initial xs v)
    (htail : LabeledWord.LegalRun v ys last) (hr : v.relaxed = true) :
    (last.selectedLeafPairsFrom (v.bodyLabels.length - 1) (v.leafIndex - 1)).card =
        last.lastSelectedLabel.card + 1 ↔
      v.bodyLabels.length < v.lastSelectedBody ∧
        (∀ k ∈ v.rootLabel, k < v.lastSelectedBody → k ≤ v.bodyLabels.length) ∧
          v.NoLeafPending := by
  have hw := hinit.cursorInvariant LabeledWord.cursorInvariant_initial
  have hstart := LabeledWord.relaxed_ne_start hw hr
  have hsel : 0 < v.leafIndex ∧ v.bodyLabels.length ∈ v.rootLabel ∧
      v.leafIndex ∈ v.currentLabel := of_decide_eq_true hr
  have hbodyPos := (hw.2.2.1 _ hsel.2.1).1
  have hbodyIndex : v.bodyLabels.length - 1 + 1 = v.bodyLabels.length := by omega
  have hleafIndex : v.leafIndex - 1 + 1 = v.leafIndex := by omega
  have hroot := htail.rootLabel_eq hstart
  have hlast : last.lastSelectedBody = v.lastSelectedBody :=
    congrArg (fun C : Finset ℕ => C.sup id) hroot
  have hbody : last.bodyLabels.getD (v.bodyLabels.length - 1) ∅ = v.currentLabel := by
    rw [htail.body_getD_eq hstart (by omega)]
    exact (LabeledWord.currentLabel_eq_getD hbodyIndex.symm).symm
  have hi : v.bodyLabels.length - 1 + 1 ∈ last.rootLabel := by
    rw [hbodyIndex, hroot]
    exact hsel.2.1
  have hj : v.leafIndex - 1 + 1 ∈ last.bodyLabels.getD (v.bodyLabels.length - 1) ∅ := by
    rw [hleafIndex, hbody]
    exact hsel.2.2
  simpa only [hbodyIndex, hleafIndex, hroot, hlast, hbody, LabeledWord.NoLeafPending] using
    h.penultimate_endpoint_iff_suffix_card hi hj

#print axioms ClearSide.relaxed_penultimate_iff_suffix_card

end Erdos591.Positive.Game.Payoff
