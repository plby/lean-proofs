import ErdosProblems.Erdos118.Reused591.MarkerPrefixAcceptance
import ErdosProblems.Erdos118.Reused591.GamePayoff

namespace Erdos118.Reused591

/-!
# Recovering the requested size of the last selected body

The last selected body is the supremum of the finite root label, with
one-based indexing. At its marker the supremum is the next body index.
The first-read label and its exact requested cardinality remain in the
same body-label slot through every subsequent legal continuation.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

def lastSelectedBody (w : LabeledWord) : ℕ := w.rootLabel.sup id

def lastSelectedLabel (w : LabeledWord) : Finset ℕ :=
  w.bodyLabels.getD (w.lastSelectedBody - 1) ∅

theorem lastSelectedBody_of_marker {w : LabeledWord} (hm : w.markerEvent = true)
    (hroot : ∀ i ∈ w.rootLabel, i ≤ w.bodyLabels.length + 1) :
    w.lastSelectedBody = w.bodyLabels.length + 1 :=
  le_antisymm (Finset.sup_le hroot) (Finset.le_sup (f := id) (marker_body_mem hm))

end LabeledWord

theorem Reply.body_label_card_after {board next : Board} {r : Request} {u : Finset ℕ}
    (hr : Reply board r u next) (hm : (board.get r.side).markerEvent = true)
    {as : List (Finset ℕ × ℕ)} {last : LabeledWord}
    (htail : LabeledWord.LegalRun (next.get r.side) as last) :
    (last.bodyLabels.getD (board.get r.side).bodyLabels.length ∅).card = r.size := by
  obtain ⟨D, n, first, bs, hcard, hread, hrun⟩ := hr.first_read
  obtain ⟨k, hparse⟩ := LabeledWord.marker_blocks hm
  rw [LabeledWord.bodyLabel_after_read hread (hrun.append htail) hparse]
  exact hcard

theorem Reply.lastSelectedLabel_card_after {board next : Board} {r : Request} {u : Finset ℕ}
    (hr : Reply board r u next) (hm : (board.get r.side).markerEvent = true)
    (hroot : ∀ i ∈ (board.get r.side).rootLabel, i ≤ (board.get r.side).bodyLabels.length + 1)
    {as : List (Finset ℕ × ℕ)} {last : LabeledWord}
    (htail : LabeledWord.LegalRun (next.get r.side) as last) :
    last.lastSelectedLabel.card = r.size := by
  obtain ⟨D, n, first, bs, _hcard, hread, hrun⟩ := hr.first_read
  obtain ⟨k, hparse⟩ := LabeledWord.marker_blocks hm
  have hstart : (board.get r.side).parser ≠ .start := by simp [hparse]
  have hrootEq : last.rootLabel = (board.get r.side).rootLabel :=
    ((hrun.append htail).rootLabel_eq (LabeledWord.read_parser_ne_start hread)).trans
      (LabeledWord.read_rootLabel_eq hread hstart)
  have hlastBody : last.lastSelectedBody = (board.get r.side).bodyLabels.length + 1 := by
    change last.rootLabel.sup id = _
    rw [hrootEq]
    exact LabeledWord.lastSelectedBody_of_marker hm hroot
  simpa [LabeledWord.lastSelectedLabel, hlastBody] using hr.body_label_card_after hm htail

namespace Payoff

open Erdos591.Negative.Exact

theorem ClearSide.lastSelectedLabel_nonempty {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) (hne : w.rootLabel.Nonempty) : w.lastSelectedLabel.Nonempty := by
  have hmem : w.lastSelectedBody ∈ w.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id) hne
  have hb := h.root_bounds w.lastSelectedBody hmem
  have hi : w.lastSelectedBody - 1 < s.val.length := by omega
  have he : w.lastSelectedBody - 1 + 1 = w.lastSelectedBody := by omega
  exact (h.root_mem_iff_body_nonempty hi).mp (by rw [he]; exact hmem)

#print axioms ClearSide.lastSelectedLabel_nonempty

end Payoff

#print axioms Reply.lastSelectedLabel_card_after

end Erdos591.Positive.Game

end Erdos118.Reused591
