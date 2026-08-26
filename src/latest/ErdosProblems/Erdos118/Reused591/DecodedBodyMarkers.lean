import ErdosProblems.Erdos118.Reused591.SelectedBodyCard
import ErdosProblems.Erdos118.Reused591.CanonicalDecode

namespace Erdos118.Reused591

/-!
# Numerical last-selected-body markers in completed literal words

The unique decoded body list supplies a total marker observable. Its
default value off the literal-word domain is irrelevant to clear pairs.
For nonempty root labels the selected marker is an actual coordinate;
disjointness therefore makes the two markers different in a clear pair.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

noncomputable def decodedBodies (w : LabeledWord) : List (List ℕ) := by
  classical
  exact if h : ∃ s : List (List ℕ), Erdos591.Negative.Exact.word s = w.coordinates
    then h.choose else []

theorem decodedBodies_eq {w : LabeledWord} {s : List (List ℕ)}
    (hs : Erdos591.Negative.Exact.word s = w.coordinates) : w.decodedBodies = s := by
  classical
  have h : ∃ t : List (List ℕ), Erdos591.Negative.Exact.word t = w.coordinates := ⟨s, hs⟩
  rw [decodedBodies, dif_pos h]
  exact Parser.word_injective (h.choose_spec.trans hs.symm)

noncomputable def lastSelectedMarker (w : LabeledWord) : ℕ :=
  (w.decodedBodies.getD (w.lastSelectedBody - 1) []).length

end LabeledWord

namespace Payoff

open Erdos591.Negative.Exact

theorem body_marker_mem_word (s : List (List ℕ)) (i : ℕ) (hi : i < s.length) :
    (s.getD i []).length ∈ word s := by
  have hmem : s.getD i [] ∈ s := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  exact ⟨s.getD i [], hmem, by simp [levelWord]⟩

theorem ClearSide.lastSelectedMarker_mem {w : LabeledWord} {s t : G}
    (h : ClearSide w s t) (hne : w.rootLabel.Nonempty) :
    w.lastSelectedMarker ∈ w.coordinates := by
  have hmem : w.lastSelectedBody ∈ w.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id) hne
  have hb := h.root_bounds _ hmem
  have hi : w.lastSelectedBody - 1 < s.val.length := by omega
  rw [LabeledWord.lastSelectedMarker, LabeledWord.decodedBodies_eq h.coordinates,
    ← h.coordinates]
  exact body_marker_mem_word s.val _ hi

theorem Clear.lastSelectedMarker_ne {board : Board} {s t : G} (h : Clear board s t)
    (hl : board.left.rootLabel.Nonempty) (hr : board.right.rootLabel.Nonempty) :
    board.left.lastSelectedMarker ≠ board.right.lastSelectedMarker := by
  intro heq
  have hleft := h.1.lastSelectedMarker_mem hl
  have hright := h.2.1.lastSelectedMarker_mem hr
  have hd : Disjoint board.left.coordinates.toFinset board.right.coordinates.toFinset := by
    simpa only [h.1.coordinates, h.2.1.coordinates] using h.2.2
  exact Finset.disjoint_left.mp hd (List.mem_toFinset.mpr hleft)
    (List.mem_toFinset.mpr (heq ▸ hright))

end Payoff

#print axioms LabeledWord.decodedBodies_eq
#print axioms Payoff.ClearSide.lastSelectedMarker_mem
#print axioms Payoff.Clear.lastSelectedMarker_ne

end Erdos591.Positive.Game

end Erdos118.Reused591
