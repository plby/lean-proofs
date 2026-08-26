import ErdosProblems.Erdos118.Reused591.NextMarkerResponse

namespace Erdos118.Reused591

/-!
# An actual response after the last current selected leaf reaches the next body

Unlike the constructive replay theorem, this direction starts with an
arbitrary accepted response. With no remaining current leaf and a least
unread root index, its endpoint must be precisely that body marker.
-/

namespace Erdos591.Positive.Game

theorem LabeledWord.NoLeafPending.remainder_marker {w v : LabeledWord} {xs : List ℕ}
    (hn : w.NoLeafPending) (hw : w.CursorInvariant) (hstart : w.parser ≠ .start)
    (hrel : w.relaxed = false) {i base : ℕ} (hs : LabeledWord.BeforeBody i w)
    (hbase : base ≤ w.bodyLabels.length)
    (hnext : ∀ k ∈ w.rootLabel, base < k → i ≤ k)
    (hr : LabeledWord.advanceRemainder.run w xs = some v) :
    v.markerEvent = true ∧ v.bodyLabels.length + 1 = i := by
  have hlu := LabeledWord.zero_run_legal _ (fun _ _ => rfl) hr
  have hbefore := hs.remainder hstart hr
  have hv := hlu.cursorInvariant hw
  have hnotterm := hbefore.not_terminal hv
  have hnotrel := (hn.zero_run hstart hrel hlu.run).2
  have hevent := LabeledWord.advanceRemainder.run_stopped hr
  have hm : v.markerEvent = true := by
    simpa [LabeledWord.advanceRemainder, LabeledWord.event, hnotterm, hnotrel] using hevent
  have hmem : v.bodyLabels.length + 1 ∈ w.rootLabel :=
    hlu.rootLabel_eq hstart ▸ LabeledWord.marker_body_mem hm
  have hlen := (hlu.bodyLabels_prefix hstart).length_le
  have hlarge := hnext _ hmem (by omega)
  exact ⟨hm, le_antisymm hbefore.2 hlarge⟩

theorem Advance.next_marker_endpoint (w : Unfinished) (hw : w.val.CursorInvariant)
    {v : LabeledWord} {xs : List ℕ} {i : ℕ}
    (hrel : w.val.relaxed = true) (hn : w.val.NoLeafPending)
    (hs : LabeledWord.BeforeBody i w.val)
    (hnext : ∀ k ∈ w.val.rootLabel, w.val.bodyLabels.length < k → i ≤ k)
    (hrun : parser.run (.prelude w 0 []) xs = some (.remainder v)) :
    v.markerEvent = true ∧ v.bodyLabels.length + 1 = i := by
  obtain ⟨labels, n, rest, first, last, _hxs, hlen, hf, hl, hlast⟩ :=
    run_prelude w 0 [] xs (.remainder v) hrun
  have heq : v = last := State.remainder.inj hlast
  subst last
  have hnil : labels = [] := List.length_eq_zero_iff.mp hlen
  have hread : w.val.read ∅ n = some first := by simpa [hnil] using hf
  have hdata := of_decide_eq_true hrel
  have hleaf : LabeledWord.UpToLeaf w.val.leafIndex w.val := ⟨hdata.2.1, hdata.2.2, le_rfl⟩
  obtain ⟨r, k, hp⟩ := hleaf.parser_leaves hw
  have hstart : w.val.parser ≠ .start := by simp [hp]
  have hfirst := hn.read hstart hread
  have hbefore := hs.read_away hstart (by simp [LabeledWord.markerEvent, hp]) hread
  have hc := hw.read (LabeledWord.allowed_empty w.property n) hread
  have he : w.val.record ∅ n (Parser.normalize r k) = first := by
    simpa [LabeledWord.read, hp, Parser.step] using hread
  have hcount : first.bodyLabels.length = w.val.bodyLabels.length := by
    simp [← he, LabeledWord.record, hp]
  have hroot : first.rootLabel = w.val.rootLabel := by
    simp [← he, LabeledWord.record, hp]
  exact hfirst.1.remainder_marker hc (LabeledWord.read_parser_ne_start hread) hfirst.2
    hbefore hcount.ge (fun j hj hjlt => hnext j (hroot ▸ hj) hjlt) hl

theorem Reply.next_marker_endpoint {board last : Board} {side : Bool} {u : Finset ℕ}
    (hr : Reply board ⟨side, .advance 0⟩ u last)
    (hw : (board.get side).CursorInvariant) (hrel : (board.get side).relaxed = true)
    (hn : (board.get side).NoLeafPending) {i : ℕ}
    (hs : LabeledWord.BeforeBody i (board.get side))
    (hnext : ∀ k ∈ (board.get side).rootLabel, (board.get side).bodyLabels.length < k → i ≤ k) :
    (last.get side).markerEvent = true ∧ (last.get side).bodyLabels.length + 1 = i := by
  cases hr with
  | advance side _ u v hlegal hrun =>
      simpa using Advance.next_marker_endpoint ⟨board.get side, hlegal.1⟩ hw
        hrel hn hs hnext hrun

#print axioms Reply.next_marker_endpoint

end Erdos591.Positive.Game

end Erdos118.Reused591
