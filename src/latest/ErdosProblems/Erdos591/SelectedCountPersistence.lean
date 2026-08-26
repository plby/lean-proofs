import ErdosProblems.Erdos591.SelectedLeafCounts
import ErdosProblems.Erdos591.CutPersistence

/-! # Counts already determined by the stored selected-body labels -/

namespace Erdos591.Positive.Game.LabeledWord

theorem LegalRun.beforeLastLeafCount_eq_of_read {w v : LabeledWord}
    {as : List (Finset ℕ × ℕ)} (h : LegalRun w as v) (hstart : w.parser ≠ .start)
    (hpos : ∀ i ∈ w.rootLabel, 0 < i)
    (hread : ∀ i ∈ w.rootLabel, i ≠ w.lastSelectedBody → i ≤ w.bodyLabels.length) :
    v.beforeLastLeafCount = w.beforeLastLeafCount := by
  have hr := h.rootLabel_eq hstart
  simp only [beforeLastLeafCount, lastSelectedBody, hr]
  apply Finset.sum_congr rfl
  intro i hi
  have himem := Finset.mem_of_mem_erase hi
  have hipos := hpos i himem
  have hibound := hread i himem (Finset.ne_of_mem_erase hi)
  rw [h.body_getD_eq hstart (by omega : i - 1 < w.bodyLabels.length)]

theorem LegalRun.beforeLastLeafCount_eq_of_last_marker {w v : LabeledWord}
    {as : List (Finset ℕ × ℕ)} (h : LegalRun w as v) (hw : w.CursorInvariant)
    (hm : w.markerEvent = true)
    (hroot : ∀ i ∈ w.rootLabel, i ≤ w.bodyLabels.length + 1) :
    v.beforeLastLeafCount = w.beforeLastLeafCount := by
  obtain ⟨r, hparse⟩ := marker_blocks hm
  apply h.beforeLastLeafCount_eq_of_read (by simp [hparse])
    (fun i hi => (hw.2.2.1 i hi).1)
  intro i hi hne
  have hiBound := hroot i hi
  rw [lastSelectedBody_of_marker hm hroot] at hne
  omega

theorem LegalRun.selectedLeafCount_eq_of_read {w v : LabeledWord}
    {as : List (Finset ℕ × ℕ)} (h : LegalRun w as v) (hstart : w.parser ≠ .start)
    (hpos : ∀ i ∈ w.rootLabel, 0 < i)
    (hread : ∀ i ∈ w.rootLabel, i ≤ w.bodyLabels.length) :
    v.selectedLeafCount = w.selectedLeafCount := by
  simp only [selectedLeafCount, h.rootLabel_eq hstart]
  apply Finset.sum_congr rfl
  intro i hi
  have hipos := hpos i hi
  have hibound := hread i hi
  rw [h.body_getD_eq hstart (by omega : i - 1 < w.bodyLabels.length)]

#print axioms LegalRun.beforeLastLeafCount_eq_of_read
#print axioms LegalRun.beforeLastLeafCount_eq_of_last_marker
#print axioms LegalRun.selectedLeafCount_eq_of_read

end Erdos591.Positive.Game.LabeledWord
