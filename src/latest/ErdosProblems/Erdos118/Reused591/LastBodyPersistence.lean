import ErdosProblems.Erdos118.Reused591.SelectedBodyCard
import ErdosProblems.Erdos118.Reused591.CutPersistence

namespace Erdos118.Reused591

/-! # Recover the already read last selected body's label in any legal continuation -/

namespace Erdos591.Positive.Game.LabeledWord

theorem LegalRun.lastSelectedLabel_eq_of_read {w v : LabeledWord}
    {as : List (Finset ℕ × ℕ)} (h : LegalRun w as v) (hstart : w.parser ≠ .start)
    (hpos : 0 < w.lastSelectedBody) (hread : w.lastSelectedBody ≤ w.bodyLabels.length) :
    v.lastSelectedLabel = w.lastSelectedLabel := by
  have hroot := h.rootLabel_eq hstart
  simp only [lastSelectedLabel, lastSelectedBody, hroot]
  exact h.body_getD_eq hstart (by change w.lastSelectedBody - 1 < w.bodyLabels.length; omega)

theorem LegalRun.lastSelectedLabel_eq_current {w v : LabeledWord}
    {as : List (Finset ℕ × ℕ)} (h : LegalRun w as v) (hw : w.CursorInvariant)
    (hr : w.relaxed = true) (hroot : ∀ i ∈ w.rootLabel, i ≤ w.bodyLabels.length) :
    v.lastSelectedLabel = w.currentLabel := by
  have hsel := (of_decide_eq_true hr).2.1
  have hpos : 0 < w.bodyLabels.length := (hw.2.2.1 _ hsel).1
  have hlast : w.lastSelectedBody = w.bodyLabels.length :=
    le_antisymm (Finset.sup_le hroot) (Finset.le_sup (f := id) hsel)
  rw [h.lastSelectedLabel_eq_of_read (relaxed_ne_start hw hr) (by omega) hlast.le]
  rw [lastSelectedLabel, hlast]
  exact (currentLabel_eq_getD (show w.bodyLabels.length = w.bodyLabels.length - 1 + 1
    from (Nat.sub_add_cancel (by omega)).symm)).symm

#print axioms LegalRun.lastSelectedLabel_eq_of_read
#print axioms LegalRun.lastSelectedLabel_eq_current

end Erdos591.Positive.Game.LabeledWord

end Erdos118.Reused591
