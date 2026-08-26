import ErdosProblems.Erdos118.Reused591.FirstMarkerResponse

namespace Erdos118.Reused591

/-!
# The first selected leaf in a selected body

Before the first selected leaf, the current body is selected, its label
is nonempty, and no label index lies below the current leaf counter.
Strict marker bounds keep the parser inside this body. The first event
is therefore a relaxed cursor at the least entry of the body label.
-/

namespace Erdos591.Positive.Game.LabeledWord

structure FirstLeafState (w : LabeledWord) : Prop where
  selected : w.bodyLabels.length ∈ w.rootLabel
  nonempty : w.currentLabel.Nonempty
  before : ∀ j ∈ w.currentLabel, w.leafIndex ≤ j

namespace FirstLeafState

theorem parser_leaves {w : LabeledWord} (h : w.FirstLeafState) (hw : w.CursorInvariant) :
    ∃ r k, w.parser = .leaves r k := by
  obtain ⟨j, hj⟩ := h.nonempty
  have hlt := (h.before j hj).trans_lt (hw.2.2.2 j hj).2
  have hc := hw.2.1.2
  have hout : 0 < outstandingLeaves w.parser := by omega
  cases hp : w.parser with
  | start => simp [hp, outstandingLeaves] at hout
  | blocks r => simp [hp, outstandingLeaves] at hout
  | leaves r k => exact ⟨r, k, rfl⟩

theorem at_event {w : LabeledWord} (h : w.FirstLeafState) (hw : w.CursorInvariant)
    (he : w.event = true) : w.relaxed = true := by
  obtain ⟨r, k, hp⟩ := h.parser_leaves hw
  simpa [event, terminal, markerEvent, hp] using he

theorem strict_before {w : LabeledWord} (h : w.FirstLeafState) (hw : w.CursorInvariant)
    (hr : w.relaxed = false) {j : ℕ} (hj : j ∈ w.currentLabel) : w.leafIndex < j := by
  have hle := h.before j hj
  by_contra hn
  have heq : w.leafIndex = j := by omega
  have hpos : 0 < w.leafIndex := heq ▸ (hw.2.2.2 j hj).1
  have hmem : w.leafIndex ∈ w.currentLabel := heq ▸ hj
  have hrel : w.relaxed = true := by
    apply decide_eq_true
    exact ⟨hpos, h.selected, hmem⟩
  simp [hr] at hrel

theorem read {w v : LabeledWord} (h : w.FirstLeafState) (hw : w.CursorInvariant)
    (he : w.event = false) {n : ℕ} (hread : w.read ∅ n = some v) : v.FirstLeafState := by
  obtain ⟨r, k, hp⟩ := h.parser_leaves hw
  have hr : w.relaxed = false := (Bool.or_eq_false_iff.mp (Bool.or_eq_false_iff.mp he).1).2
  have heq : w.record ∅ n (Parser.normalize r k) = v := by
    simpa [LabeledWord.read, hp, Parser.step] using hread
  subst v
  constructor
  · simpa [record, hp] using h.selected
  · simpa [currentLabel, record, hp] using h.nonempty
  · intro j hj
    have hj' : j ∈ w.currentLabel := by simpa [currentLabel, record, hp] using hj
    simpa [record, hp] using h.strict_before hw hr hj'

theorem remainder {w v : LabeledWord} {xs : List ℕ}
    (h : w.FirstLeafState) (hw : w.CursorInvariant)
    (hrun : advanceRemainder.run w xs = some v) : v.FirstLeafState := by
  induction xs generalizing w with
  | nil =>
      cases he : w.event with
      | false => simp [ResponseParser.run, advanceRemainder, he] at hrun
      | true =>
          have heq : w = v := by simpa [ResponseParser.run, advanceRemainder, he] using hrun
          exact heq ▸ h
  | cons n xs ih =>
      cases he : w.event with
      | true => simp [ResponseParser.run, advanceRemainder, he] at hrun
      | false =>
          obtain ⟨u, hu⟩ := read_exists (event_false_terminal he) ∅ n
          have ht : advanceRemainder.run u xs = some v := by
            simpa [ResponseParser.run, advanceRemainder, he, hu] using hrun
          exact ih (h.read hw he hu) (hw.read (allowed_empty (read_nonterminal hu) n) hu) ht

theorem remainder_bodyLabels {w v : LabeledWord} {xs : List ℕ}
    (h : w.FirstLeafState) (hw : w.CursorInvariant)
    (hrun : advanceRemainder.run w xs = some v) : v.bodyLabels = w.bodyLabels := by
  induction xs generalizing w with
  | nil =>
      cases he : w.event with
      | false => simp [ResponseParser.run, advanceRemainder, he] at hrun
      | true =>
          have heq : w = v := by simpa [ResponseParser.run, advanceRemainder, he] using hrun
          exact congrArg LabeledWord.bodyLabels heq.symm
  | cons n xs ih =>
      cases he : w.event with
      | true => simp [ResponseParser.run, advanceRemainder, he] at hrun
      | false =>
          obtain ⟨u, hu⟩ := read_exists (event_false_terminal he) ∅ n
          have ht : advanceRemainder.run u xs = some v := by
            simpa [ResponseParser.run, advanceRemainder, he, hu] using hrun
          have hv := ih (h.read hw he hu) (hw.read (allowed_empty (read_nonterminal hu) n) hu) ht
          obtain ⟨r, k, hp⟩ := h.parser_leaves hw
          have heq : w.record ∅ n (Parser.normalize r k) = u := by
            simpa [LabeledWord.read, hp, Parser.step] using hu
          rw [hv, ← heq]
          simp [record, hp]

theorem remainder_minimum {w v : LabeledWord} {xs : List ℕ}
    (h : w.FirstLeafState) (hw : w.CursorInvariant)
    (hrun : advanceRemainder.run w xs = some v) :
    v.relaxed = true ∧ v.leafIndex ∈ v.currentLabel ∧
      ∀ j ∈ v.currentLabel, v.leafIndex ≤ j := by
  have hv := h.remainder hw hrun
  have hcorrect := advanceRemainder_invariant hw hrun
  have he := advanceRemainder.run_stopped hrun
  have hr : v.relaxed = true := hv.at_event hcorrect he
  have hsel : 0 < v.leafIndex ∧ v.bodyLabels.length ∈ v.rootLabel ∧
      v.leafIndex ∈ v.currentLabel := by simpa [relaxed] using hr
  exact ⟨hr, hsel.2.2, hv.before⟩

theorem of_marker_read {w v : LabeledWord} {D : Finset ℕ} {n : ℕ}
    (hm : w.markerEvent = true) (hD : D.Nonempty) (hr : w.read D n = some v) :
    v.FirstLeafState := by
  cases hp : w.parser with
  | start => simp [markerEvent, hp] at hm
  | leaves r k => simp [markerEvent, hp] at hm
  | blocks r =>
      cases r with
      | zero => simp [markerEvent, hp] at hm
      | succ r =>
          have hsel : w.bodyLabels.length + 1 ∈ w.rootLabel := by
            simpa [markerEvent, hp] using hm
          have heq : w.record D n (Parser.normalize r n) = v := by
            simpa [LabeledWord.read, hp, Parser.step] using hr
          subst v
          constructor
          · simpa [record, hp] using hsel
          · simpa [record, hp, currentLabel] using hD
          · simp [record, hp]

#print axioms remainder_minimum
#print axioms remainder_bodyLabels

end FirstLeafState

end Erdos591.Positive.Game.LabeledWord

namespace Erdos591.Positive.Game.Advance

theorem selected_positive_first_leaf (w : Unfinished) (hw : w.val.CursorInvariant)
    (hm : w.val.markerEvent = true) (d : ℕ) (hd : 0 < d) (xs : List ℕ) (v : LabeledWord)
    (hinc : xs.Pairwise (· < ·)) (hpos : ∀ x ∈ xs, 0 < x)
    (hrun : parser.run (.prelude w d []) xs = some (.remainder v)) :
    v.relaxed = true ∧ v.leafIndex ∈ v.currentLabel ∧
      ∀ j ∈ v.currentLabel, v.leafIndex ≤ j := by
  obtain ⟨labels, n, rest, first, last, hxs, hlen, hf, hl, hlast⟩ :=
    run_prelude w d [] xs (.remainder v) hrun
  have heq : v = last := State.remainder.inj hlast
  subst last
  have hp : (labels ++ n :: rest).Pairwise (· < ·) := hxs ▸ hinc
  have hcard : labels.toFinset.card = d :=
    (List.toFinset_card_of_nodup (List.pairwise_append.mp hp).1.nodup).trans hlen
  have hbound : ∀ i ∈ labels.toFinset, 0 < i ∧ i < n := by
    intro i hi
    have hil : i ∈ labels := List.mem_toFinset.mp hi
    exact ⟨hpos i (hxs ▸ List.mem_append_left _ hil),
      (List.pairwise_append.mp hp).2.2 i hil n (by simp)⟩
  have hread : w.val.read labels.toFinset n = some first := by simpa using hf
  have hsize : w.val.AllowedSize d := ⟨w.property, Or.inr (Or.inr hm)⟩
  have hlabel := LabeledWord.allowedLabel_of_size hsize hcard hbound
  have hstate := LabeledWord.FirstLeafState.of_marker_read hm
    (Finset.card_pos.mp (hcard ▸ hd)) hread
  exact hstate.remainder_minimum (hw.read hlabel hread) hl

#print axioms selected_positive_first_leaf

end Erdos591.Positive.Game.Advance

end Erdos118.Reused591
