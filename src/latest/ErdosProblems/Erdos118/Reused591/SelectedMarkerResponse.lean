import ErdosProblems.Erdos118.Reused591.LeafPrefixAcceptance

namespace Erdos118.Reused591

/-!
# Numerical marker and body count of a selected positive response

The response decomposition identifies the actual marker input. Before
the first selected leaf, the body label list and marker do not change.
Thus the marker's freshness follows from membership in the response.
-/

namespace Erdos591.Positive.Game.Advance

theorem selected_marker_metadata (w : Unfinished) (hw : w.val.CursorInvariant)
    (hm : w.val.markerEvent = true) (d : ℕ) (hd : 0 < d) (xs : List ℕ) (v : LabeledWord)
    (hinc : xs.Pairwise (· < ·)) (hpos : ∀ x ∈ xs, 0 < x)
    (hrun : parser.run (.prelude w d []) xs = some (.remainder v)) :
    v.relaxed = true ∧ v.bodyLabels.length = w.val.bodyLabels.length + 1 ∧
      v.bodyMarker ∈ xs := by
  obtain ⟨labels, n, rest, first, last, hxs, hlen, hf, hl, hlast⟩ :=
    run_prelude w d [] xs (.remainder v) hrun
  have heq : v = last := State.remainder.inj hlast
  subst last
  have hp : (labels ++ n :: rest).Pairwise (· < ·) := hxs ▸ hinc
  have hcard : labels.toFinset.card = d :=
    (List.toFinset_card_of_nodup (List.pairwise_append.mp hp).1.nodup).trans hlen
  have hbound : ∀ i ∈ labels.toFinset, 0 < i ∧ i < n := by
    intro i hi
    have hil := List.mem_toFinset.mp hi
    exact ⟨hpos i (hxs ▸ List.mem_append_left _ hil),
      (List.pairwise_append.mp hp).2.2 i hil n (by simp)⟩
  have hread : w.val.read labels.toFinset n = some first := by simpa using hf
  have hsize : w.val.AllowedSize d := ⟨w.property, Or.inr (Or.inr hm)⟩
  have hlabel := LabeledWord.allowedLabel_of_size hsize hcard hbound
  have hstate := LabeledWord.FirstLeafState.of_marker_read hm
    (Finset.card_pos.mp (hcard ▸ hd)) hread
  have hfirst := hw.read hlabel hread
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hm
  have hrecord : w.val.record labels.toFinset n (Parser.normalize r n) = first := by
    simpa [LabeledWord.read, hparse, Parser.step] using hread
  refine ⟨(hstate.remainder_minimum hfirst hl).1, ?_, ?_⟩
  · rw [hstate.remainder_bodyLabels hfirst hl, ← hrecord]
    simp [LabeledWord.record, hparse]
  · rw [hstate.remainder_bodyMarker hfirst hl, ← hrecord]
    simp [LabeledWord.record, hparse, hxs]

#print axioms selected_marker_metadata

end Erdos591.Positive.Game.Advance

namespace Erdos591.Positive.Game

theorem Reply.selected_marker_metadata {board next : Board} {side : Bool} {d : ℕ}
    {u : Finset ℕ} (hr : Reply board ⟨side, .advance d⟩ u next)
    (hw : (board.get side).CursorInvariant) (hm : (board.get side).markerEvent = true)
    (hd : 0 < d) (hpos : ∀ x ∈ u, 0 < x) :
    (next.get side).relaxed = true ∧
      (next.get side).bodyLabels.length = (board.get side).bodyLabels.length + 1 ∧
      (next.get side).bodyMarker ∈ u := by
  cases hr with
  | advance s d u w hlegal hrun =>
      simpa using Advance.selected_marker_metadata ⟨board.get side, hlegal.1⟩ hw hm d hd
        (u.sort (· ≤ ·)) w (Finset.sortedLT_sort u).pairwise
        (fun x hx => hpos x (by simpa using hx)) hrun

#print axioms Reply.selected_marker_metadata

end Erdos591.Positive.Game

end Erdos118.Reused591
