import ErdosProblems.Erdos118.Reused591.NextMarkerAcceptance
import ErdosProblems.Erdos118.Reused591.RootGluing

namespace Erdos118.Reused591

/-! # The actual advance response from a last current leaf to the next selected body -/

namespace Erdos591.Positive.Game

namespace Advance

theorem zero_to_next_marker (w : Unfinished) (hw : w.val.CursorInvariant)
    {v : LabeledWord} {xs : List ℕ} {i : ℕ}
    (hrel : w.val.relaxed = true) (hn : w.val.NoLeafPending)
    (hs : LabeledWord.BeforeBody i w.val)
    (hnext : ∀ k ∈ w.val.rootLabel, w.val.bodyLabels.length < k → i ≤ k)
    (hraw : w.val.runAtoms (xs.map fun n => (∅, n)) = some v)
    (hv : v.markerEvent = true) (hindex : v.bodyLabels.length + 1 = i) :
    parser.run (.prelude w 0 []) xs = some (.remainder v) := by
  have hdata := of_decide_eq_true hrel
  have hleaf : LabeledWord.UpToLeaf w.val.leafIndex w.val := ⟨hdata.2.1, hdata.2.2, le_rfl⟩
  obtain ⟨r, k, hp⟩ := hleaf.parser_leaves hw
  have hstart : w.val.parser ≠ .start := by simp [hp]
  cases xs with
  | nil =>
      have he : w.val = v := Option.some.inj hraw
      simp [← he, LabeledWord.markerEvent, hp] at hv
  | cons n xs =>
      cases hread : w.val.read ∅ n with
      | none => simp [LabeledWord.runAtoms, hread] at hraw
      | some first =>
          have ht : first.runAtoms (xs.map fun n => (∅, n)) = some v := by
            simpa [LabeledWord.runAtoms, hread] using hraw
          have hfirst := hn.read hstart hread
          have hbefore := hs.read_away hstart (by simp [LabeledWord.markerEvent, hp]) hread
          have hc := hw.read (LabeledWord.allowed_empty w.property n) hread
          have he : w.val.record ∅ n (Parser.normalize r k) = first := by
            simpa [LabeledWord.read, hp, Parser.step] using hread
          have hlen : first.bodyLabels.length = w.val.bodyLabels.length := by
            simp [← he, LabeledWord.record, hp]
          have hroot : first.rootLabel = w.val.rootLabel := by
            simp [← he, LabeledWord.record, hp]
          have hrest := LabeledWord.advanceRemainder_to_next_marker hc
            (LabeledWord.read_parser_ne_start hread) hfirst.1 hfirst.2 hbefore hlen.ge
            (fun j hj hjlt => hnext j (hroot ▸ hj) hjlt) ht hv hindex
          simpa using run_prelude_build w [] [] n xs first v (by simpa using hread) hrest

end Advance

theorem Reply.next_marker_of_list (board : Board) (side : Bool) {v : LabeledWord}
    {xs : List ℕ} {i : ℕ} (hw : (board.get side).CursorInvariant)
    (hrel : (board.get side).relaxed = true) (hn : (board.get side).NoLeafPending)
    (hs : LabeledWord.BeforeBody i (board.get side))
    (hnext : ∀ k ∈ (board.get side).rootLabel, (board.get side).bodyLabels.length < k → i ≤ k)
    (hraw : (board.get side).runAtoms (xs.map fun n => (∅, n)) = some v)
    (hv : v.markerEvent = true) (hindex : v.bodyLabels.length + 1 = i)
    (hinc : xs.Pairwise (· < ·)) :
    Reply board ⟨side, .advance 0⟩ xs.toFinset (board.update side v) := by
  have hlive := LabeledWord.relaxed_not_terminal hw.2.1 hw.2.2 hrel
  apply Reply.advance side 0 xs.toFinset v ⟨hlive, Or.inl rfl⟩
  rw [Erdos590.Larson.sort_toFinset_eq_self_of_pairwise hinc]
  exact Advance.zero_to_next_marker ⟨board.get side, hlive⟩ hw hrel hn hs hnext hraw hv hindex

#print axioms Reply.next_marker_of_list

end Erdos591.Positive.Game

end Erdos118.Reused591
