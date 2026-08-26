import ErdosProblems.Erdos118.Reused591.LeafPrefixAcceptance

namespace Erdos118.Reused591

/-!
# Advance responses cannot pass a prescribed selected leaf

The current selected body and one of its leaf-label entries are fixed.
Until this entry is reached, each read stays inside this body. Reaching
the entry creates an event, so the first-event remainder cannot pass it.
The actual response preserves the whole stored body-label list and marker.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

structure UpToLeaf (j : ℕ) (w : LabeledWord) : Prop where
  selected : w.bodyLabels.length ∈ w.rootLabel
  mem : j ∈ w.currentLabel
  before : w.leafIndex ≤ j

namespace UpToLeaf

theorem parser_leaves {j : ℕ} {w : LabeledWord} (h : UpToLeaf j w)
    (hw : w.CursorInvariant) : ∃ r k, w.parser = .leaves r k := by
  have hlt := h.before.trans_lt (hw.2.2.2 j h.mem).2
  have hc := hw.2.1.2
  have hout : 0 < outstandingLeaves w.parser := by omega
  cases hp : w.parser with
  | start => simp [hp, outstandingLeaves] at hout
  | blocks r => simp [hp, outstandingLeaves] at hout
  | leaves r k => exact ⟨r, k, rfl⟩

theorem relaxed_of_eq {j : ℕ} {w : LabeledWord} (h : UpToLeaf j w)
    (hw : w.CursorInvariant) (heq : w.leafIndex = j) : w.relaxed = true := by
  apply decide_eq_true
  exact ⟨heq ▸ (hw.2.2.2 j h.mem).1, h.selected, heq ▸ h.mem⟩

theorem strict_before {j : ℕ} {w : LabeledWord} (h : UpToLeaf j w)
    (hw : w.CursorInvariant) (he : w.event = false) : w.leafIndex < j := by
  have hne : w.leafIndex ≠ j := by
    intro heq
    have hr := h.relaxed_of_eq hw heq
    simp [event, hr] at he
  exact lt_of_le_of_ne h.before hne

theorem read_before {j : ℕ} {w v : LabeledWord} {D : Finset ℕ} {n : ℕ}
    (h : UpToLeaf j w) (hw : w.CursorInvariant) (hlt : w.leafIndex < j)
    (hr : w.read D n = some v) :
    UpToLeaf j v ∧ v.bodyLabels = w.bodyLabels ∧ v.bodyMarker = w.bodyMarker := by
  obtain ⟨r, k, hp⟩ := h.parser_leaves hw
  have heq : w.record D n (Parser.normalize r k) = v := by
    simpa [LabeledWord.read, hp, Parser.step] using hr
  subst v
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simpa [record, hp] using h.selected
  · simpa [record, hp, currentLabel] using h.mem
  · simpa [record, hp] using hlt
  · simp [record, hp]
  · simp [record, hp]

theorem remainder {j : ℕ} {w v : LabeledWord} {xs : List ℕ}
    (h : UpToLeaf j w) (hw : w.CursorInvariant)
    (hr : advanceRemainder.run w xs = some v) :
    UpToLeaf j v ∧ v.bodyLabels = w.bodyLabels ∧ v.bodyMarker = w.bodyMarker := by
  induction xs generalizing w with
  | nil =>
      cases he : w.event with
      | false => simp [ResponseParser.run, advanceRemainder, he] at hr
      | true =>
          have heq : w = v := by simpa [ResponseParser.run, advanceRemainder, he] using hr
          subst v
          exact ⟨h, rfl, rfl⟩
  | cons n xs ih =>
      cases he : w.event with
      | true => simp [ResponseParser.run, advanceRemainder, he] at hr
      | false =>
          obtain ⟨u, hu⟩ := read_exists (event_false_terminal he) ∅ n
          have ht : advanceRemainder.run u xs = some v := by
            simpa [ResponseParser.run, advanceRemainder, he, hu] using hr
          have hread := h.read_before hw (h.strict_before hw he) hu
          have hv := ih hread.1 (hw.read (allowed_empty (read_nonterminal hu) n) hu) ht
          exact ⟨hv.1, hv.2.1.trans hread.2.1, hv.2.2.trans hread.2.2⟩

end UpToLeaf

end LabeledWord

namespace Advance

theorem up_to_leaf (w : Unfinished) (hw : w.val.CursorInvariant) (d : ℕ)
    (xs : List ℕ) (v : LabeledWord) {j : ℕ}
    (h : LabeledWord.UpToLeaf j w.val) (hlt : w.val.leafIndex < j)
    (hlegal : w.val.AllowedSize d)
    (hr : parser.run (.prelude w d []) xs = some (.remainder v)) :
    LabeledWord.UpToLeaf j v ∧ v.bodyLabels = w.val.bodyLabels ∧
      v.bodyMarker = w.val.bodyMarker := by
  obtain ⟨r, k, hp⟩ := h.parser_leaves hw
  have hd : d = 0 := by
    rcases hlegal.2 with hd | hs | hm
    · exact hd
    · simp [hp] at hs
    · simp [LabeledWord.markerEvent, hp] at hm
  subst d
  obtain ⟨labels, n, rest, first, last, _, hlen, hf, hl, hlast⟩ :=
    run_prelude w 0 [] xs (.remainder v) hr
  have hnil : labels = [] := List.length_eq_zero_iff.mp hlen
  have heq : v = last := State.remainder.inj hlast
  subst last
  have hread : w.val.read ∅ n = some first := by simpa [hnil] using hf
  have hfirst := h.read_before hw hlt hread
  have hv := hfirst.1.remainder (hw.read (LabeledWord.allowed_empty w.property n) hread) hl
  exact ⟨hv.1, hv.2.1.trans hfirst.2.1, hv.2.2.trans hfirst.2.2⟩

end Advance

theorem Reply.advance_up_to_leaf {board last : Board} {side : Bool} {d j : ℕ}
    {u : Finset ℕ} (hr : Reply board ⟨side, .advance d⟩ u last)
    (hw : (board.get side).CursorInvariant) (h : LabeledWord.UpToLeaf j (board.get side))
    (hlt : (board.get side).leafIndex < j) :
    LabeledWord.UpToLeaf j (last.get side) ∧
      (last.get side).bodyLabels = (board.get side).bodyLabels ∧
      (last.get side).bodyMarker = (board.get side).bodyMarker := by
  cases hr with
  | advance side d u v hlegal hrun =>
      simpa using Advance.up_to_leaf ⟨board.get side, hlegal.1⟩ hw d
        (u.sort (· ≤ ·)) v h hlt hlegal hrun

#print axioms Reply.advance_up_to_leaf

end Erdos591.Positive.Game

end Erdos118.Reused591
