import ErdosProblems.Erdos118.Reused591.LabeledPrefix
import ErdosProblems.Erdos118.Reused591.TargetLeaf
import ErdosProblems.Erdos118.Reused591.FastSequence

namespace Erdos118.Reused591

/-!
# Extend a virtual same-body cursor to an unread selected leaf

Only new leaf coordinates are chosen, above the supplied bound and all
old coordinates. Their number is exactly the difference of leaf indices.
The original root and body labels, and both markers, remain unchanged.
-/

namespace Erdos591.Positive.Game.LabeledWord

theorem fresh_leaf_extension {H : Set ℕ} (hH : H.Infinite) (w : LabeledWord)
    (hw : w.CursorInvariant) (hinc : w.coordinates.Pairwise (· < ·)) {j : ℕ}
    (hup : UpToLeaf j w) (hstrict : w.leafIndex < j) (B : ℕ) :
    ∃ ys v, LegalRun w (ys.map fun y => (∅, y)) v ∧
      v.relaxed = true ∧ v.leafIndex = j ∧ v.bodyLabels = w.bodyLabels ∧
      v.bodyMarker = w.bodyMarker ∧ v.rootLabel = w.rootLabel ∧
      ys.length = j - w.leafIndex ∧ v.coordinates = w.coordinates ++ ys ∧
      v.coordinates.Pairwise (· < ·) ∧
      (∀ y ∈ ys, y ∈ H ∧ B < y) ∧
      ∀ x ∈ w.coordinates, ∀ y ∈ ys, x < y := by
  classical
  let C := max B (w.coordinates.toFinset.sup id)
  obtain ⟨f, hf, hfH, hfC, _⟩ := FastSequence.exists_above_finite_bounds hH ∅ (fun _ => C)
  let F := (Finset.range (j - w.leafIndex)).image f
  let ys := F.sort (· ≤ ·)
  have hlen : ys.length = j - w.leafIndex := by
    simp [ys, F, Finset.card_image_of_injective _ hf.injective]
  have hfresh : ∀ y ∈ ys, y ∈ H ∧ C < y := by
    intro y hy
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp ((Finset.mem_sort (· ≤ ·)).mp hy)
    exact ⟨hfH i, hfC i⟩
  have hafter : ∀ x ∈ w.coordinates, ∀ y ∈ ys, x < y := by
    intro x hx y hy
    have hxle : x ≤ C := (Finset.le_sup (f := id) (List.mem_toFinset.mpr hx)).trans
      (le_max_right _ _)
    exact hxle.trans_lt (hfresh y hy).2
  obtain ⟨r, k, hparse⟩ := hup.parser_leaves hw
  have hcounter : w.leafIndex + (k + 1) = w.bodyMarker := by
    have hc := hw.2.1.2
    simpa only [hparse, outstandingLeaves] using hc
  have hjbound : j < w.bodyMarker := (hw.2.2.2 j hup.mem).2
  have hsum : ys.length + (w.bodyMarker - j) = k + 1 := by omega
  let v : LabeledWord := { w with
    parser := Parser.normalize r (w.bodyMarker - j)
    coordinates := w.coordinates ++ ys
    leafIndex := w.leafIndex + ys.length }
  have hraw : w.runAtoms (ys.map fun y => (∅, y)) = some v :=
    runAtoms_leaves_part w r (w.bodyMarker - j) ys
      (by rw [hsum]; simpa [Parser.normalize] using hparse)
  have hrun := legal_of_zero_atoms hraw
  have hidx : v.leafIndex = j := by change w.leafIndex + ys.length = j; omega
  have hvup : UpToLeaf j v := ⟨hup.selected, hup.mem, hidx.le⟩
  refine ⟨ys, v, hrun, hvup.relaxed_of_eq (hrun.cursorInvariant hw) hidx, hidx,
    rfl, rfl, rfl, hlen, rfl, ?_, ?_, hafter⟩
  · exact List.pairwise_append.mpr ⟨hinc, (Finset.sortedLT_sort F).pairwise, hafter⟩
  · intro y hy
    exact ⟨(hfresh y hy).1, (le_max_left _ _).trans_lt (hfresh y hy).2⟩

#print axioms fresh_leaf_extension

end Erdos591.Positive.Game.LabeledWord

end Erdos118.Reused591
