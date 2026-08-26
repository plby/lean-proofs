import ErdosProblems.Erdos118.Reused591.RootGluing
import ErdosProblems.Erdos118.Reused591.LeafPrefixAcceptance

namespace Erdos118.Reused591

/-!
# The actual upper response in last--first leaf gluing

At a selected body marker, prescribing a coordinate prefix whose length
is the least new body-label entry gives the exact first selected-leaf
response. Thus the last lower leaf and first upper leaf can use the same
coordinates while retaining their independently fixed body labels.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

def bodyLeafCursor (w : LabeledWord) (D : Finset ℕ) (n r : ℕ) (xs : List ℕ) :
    LabeledWord :=
  { parser := Parser.normalize r (n - xs.length)
    coordinates := w.coordinates ++ n :: xs
    rootLabel := w.rootLabel
    bodyLabels := w.bodyLabels ++ [D]
    leafIndex := xs.length
    rootMarker := w.rootMarker
    bodyMarker := n }

theorem bodyLeafCursor_run (w : LabeledWord) (D : Finset ℕ) (n r : ℕ) (xs : List ℕ)
    (hp : w.parser = .blocks (r + 1)) (hlen : xs.length ≤ n) :
    w.runAtoms ((D, n) :: xs.map fun x => (∅, x)) = some (bodyLeafCursor w D n r xs) := by
  let first := w.record D n (Parser.normalize r n)
  have hr : w.read D n = some first := by simp [LabeledWord.read, hp, Parser.step, first]
  have hparse : first.parser = Parser.normalize r (xs.length + (n - xs.length)) := by
    simp [first, record, Nat.add_sub_of_le hlen]
  have htail := runAtoms_leaves_part first r (n - xs.length) xs hparse
  simpa [runAtoms, hr, first, record, hp, bodyLeafCursor, List.append_assoc] using htail

theorem bodyLeafCursor_first_event (w : LabeledWord) (D : Finset ℕ) (n r : ℕ)
    (xs : List ℕ) (hw : w.CursorInvariant) (hp : w.parser = .blocks (r + 1))
    (hm : w.markerEvent = true) (hD : ∀ i ∈ D, 0 < i ∧ i < n)
    (hi : xs.length ∈ D) (hmin : ∀ i ∈ D, xs.length ≤ i) :
    advanceRemainder.run (w.record D n (Parser.normalize r n)) xs =
      some (bodyLeafCursor w D n r xs) := by
  let first := w.record D n (Parser.normalize r n)
  have hr : w.read D n = some first := by simp [LabeledWord.read, hp, Parser.step, first]
  have hlegal : w.AllowedLabel D n :=
    allowedLabel_of_size ⟨marker_not_terminal hm, Or.inr (Or.inr hm)⟩ rfl hD
  have hcorrect := hw.read hlegal hr
  have hs := FirstLeafState.of_marker_read hm ⟨xs.length, hi⟩ hr
  have hlen := (hD xs.length hi).2.le
  have hrun := bodyLeafCursor_run w D n r xs hp hlen
  have hraw : first.runAtoms (xs.map fun x => (∅, x)) =
      some (bodyLeafCursor w D n r xs) := by
    simpa [runAtoms, hr] using hrun
  have hsel : w.bodyLabels.length + 1 ∈ w.rootLabel := marker_body_mem hm
  have hrel : (bodyLeafCursor w D n r xs).relaxed = true := by
    simpa [relaxed, bodyLeafCursor, currentLabel] using
      (show 0 < xs.length ∧ w.bodyLabels.length + 1 ∈ w.rootLabel ∧ xs.length ∈ D from
        ⟨(hD xs.length hi).1, hsel, hi⟩)
  have hstate : (bodyLeafCursor w D n r xs).FirstLeafState := by
    constructor
    · simpa [bodyLeafCursor] using hsel
    · simpa [bodyLeafCursor, currentLabel] using (show D.Nonempty from ⟨xs.length, hi⟩)
    · simpa [bodyLeafCursor, currentLabel] using hmin
  exact advanceRemainder_to_first_leaf hcorrect hs hraw hrel hstate
    (by simp [bodyLeafCursor, record, hp])
    (by simp [bodyLeafCursor, record, hp])

end LabeledWord

namespace LastFirstLabels

theorem leaf_reply {H : Set ℕ} {B a c : ℕ} (L : LastFirstLabels H B a c)
    (board : Board) (side : Bool) (r : ℕ) (xs : List ℕ)
    (hw : (board.get side).CursorInvariant)
    (hp : (board.get side).parser = .blocks (r + 1))
    (hm : (board.get side).markerEvent = true) (hlen : xs.length = L.pivot)
    (hinc : (L.marker :: xs).Pairwise (· < ·)) (hpool : ∀ x ∈ xs, x ∈ H) :
    ∃ u, Reply board ⟨side, .advance c⟩ u
        (board.update side (LabeledWord.bodyLeafCursor (board.get side) L.upper L.marker r xs)) ∧
      u.sort (· ≤ ·) = L.upper.sort (· ≤ ·) ++ L.marker :: xs ∧
      (↑u : Set ℕ) ⊆ H ∧ ∀ x ∈ u, B < x := by
  have hrest := LabeledWord.bodyLeafCursor_first_event (board.get side) L.upper L.marker r xs
    hw hp hm L.label_bounds.2 (hlen ▸ L.pivot_upper) (fun i hi => hlen ▸ L.upper_ge i hi)
  let input := L.upper.sort (· ≤ ·) ++ L.marker :: xs
  have hinput : input.Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨(Finset.sortedLT_sort L.upper).pairwise, hinc, ?_⟩
    intro x hx y hy
    have hxm := (L.upper_fresh x ((Finset.mem_sort (· ≤ ·)).mp hx)).2.2
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hxm
    · exact hxm.trans ((List.pairwise_cons.mp hinc).1 y hy)
  have hlegal : (board.get side).AllowedSize L.upper.card :=
    ⟨LabeledWord.marker_not_terminal hm, Or.inr (Or.inr hm)⟩
  have hread : (board.get side).read L.upper L.marker =
      some ((board.get side).record L.upper L.marker (Parser.normalize r L.marker)) := by
    simp [LabeledWord.read, hp, Parser.step]
  have hreply := Reply.advance_of_list board side L.upper L.marker xs _ _
    hlegal hread hrest hinput
  rw [L.upper_card] at hreply
  have hvalues : ∀ x ∈ input, x ∈ H ∧ B < x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hf := L.upper_fresh x ((Finset.mem_sort (· ≤ ·)).mp hx)
      exact ⟨hf.1, hf.2.1⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact L.marker_fresh
      · exact ⟨hpool x hx, L.marker_fresh.2.trans ((List.pairwise_cons.mp hinc).1 x hx)⟩
  exact ⟨input.toFinset, hreply, Erdos590.Larson.sort_toFinset_eq_self_of_pairwise hinput,
    fun x hx => (hvalues x (List.mem_toFinset.mp hx)).1,
    fun x hx => (hvalues x (List.mem_toFinset.mp hx)).2⟩

#print axioms leaf_reply

end LastFirstLabels

end Erdos591.Positive.Game

end Erdos118.Reused591
