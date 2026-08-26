import ErdosProblems.Erdos591.DecodedBodyMarkers
import ErdosProblems.Erdos591.WordPositions
import ErdosProblems.Erdos591.CutPersistence

/-!
# Recovering a selected body's marker from its completed continuation

A relaxed prefix ends at a genuine leaf of the uniquely decoded word.
Its current body marker is the length of that decoded body. When the
current body is the last selected one, this is the terminal observable,
even if the mutable current-body marker later advances to another body.
-/

namespace Erdos591.Positive.Game.LabeledWord

open Erdos591.Negative.Exact

theorem LegalRun.bodyMarker_of_relaxed_prefix
    {v last : LabeledWord} {xs ys : List (Finset ℕ × ℕ)}
    (hinit : LegalRun initial xs v) (htail : LegalRun v ys last)
    (s : List (List ℕ)) (hs : word s = last.coordinates)
    (hr : v.relaxed = true) :
    v.bodyMarker = (s.getD (v.bodyLabels.length - 1) []).length := by
  have hpos := hinit.relaxed_coordinates_pos hr
  have hprefix : List.IsPrefix v.coordinates (word s) := hs ▸ htail.coordinates_prefix
  have hlen := hprefix.length_le
  have heq : v.coordinates = (word s).take (v.coordinates.length - 1 + 1) := by
    rw [Nat.sub_add_cancel (by omega)]
    exact List.prefix_iff_eq_take.mp hprefix
  obtain ⟨i, j, _hi, _hj, hbody, _hleaf, _hroot, hmarker, _hposition⟩ :=
    LabeledCode.relaxed_prefix_indices hinit s (v.coordinates.length - 1) heq
      (by omega) hr
  simpa only [hbody, Nat.add_sub_cancel] using hmarker

theorem LegalRun.lastSelectedMarker_of_relaxed_prefix
    {v last : LabeledWord} {xs ys : List (Finset ℕ × ℕ)}
    (hinit : LegalRun initial xs v) (htail : LegalRun v ys last)
    (s : List (List ℕ)) (hs : word s = last.coordinates)
    (hr : v.relaxed = true) (hcurrent : v.lastSelectedBody = v.bodyLabels.length) :
    last.lastSelectedMarker = v.bodyMarker := by
  have hstart := relaxed_ne_start (hinit.cursorInvariant cursorInvariant_initial) hr
  have hroot := htail.rootLabel_eq hstart
  have hbody : last.lastSelectedBody = v.bodyLabels.length := by
    simpa only [lastSelectedBody, hroot] using hcurrent
  rw [lastSelectedMarker, decodedBodies_eq hs, hbody]
  exact (hinit.bodyMarker_of_relaxed_prefix htail s hs hr).symm

#print axioms LegalRun.bodyMarker_of_relaxed_prefix
#print axioms LegalRun.lastSelectedMarker_of_relaxed_prefix

end Erdos591.Positive.Game.LabeledWord

namespace Erdos591.Positive.Game.History

theorem lastSelectedMarker_eq_of_relaxed_prefix {N : Set ℕ} {p z : Concrete.Hist N}
    (hpath : Relation.ReflTransGen (fun p q => History.Next q p) p z)
    (hdone : Concrete.done z.position.board = true) (side : Bool)
    (hr : (p.position.board.get side).relaxed = true)
    (hcurrent : (p.position.board.get side).lastSelectedBody =
      (p.position.board.get side).bodyLabels.length) :
    (z.position.board.get side).lastSelectedMarker =
      (p.position.board.get side).bodyMarker := by
  obtain ⟨xs, hx⟩ := word_run p side
  obtain ⟨ys, hy, _⟩ := (reachable_word_extension hpath).2 side
  have hw := (Position.history_dataInvariant z).2.1 side
  obtain ⟨s, hs⟩ := LabeledWord.terminal_good hw.1.1 hw.2
    (z.position.board.terminal_of_done hdone side)
  exact hx.lastSelectedMarker_of_relaxed_prefix hy s.val hs hr hcurrent

#print axioms lastSelectedMarker_eq_of_relaxed_prefix

end Erdos591.Positive.Game.History
