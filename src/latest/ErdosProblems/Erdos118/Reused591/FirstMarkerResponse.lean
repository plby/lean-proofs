import ErdosProblems.Erdos118.Reused591.FinalTailResponse

namespace Erdos118.Reused591

/-!
# The first event with empty body labels

A positive root label leaves a selected body pending. During the
opening remainder all body labels are empty, so no selected leaf can
be reached. The first event is therefore a selected-body marker,
not completion or a selected leaf.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

def EmptyBodies (w : LabeledWord) : Prop := ∀ D ∈ w.bodyLabels, D = ∅

theorem EmptyBodies.current_empty {w : LabeledWord} (h : w.EmptyBodies) :
    w.currentLabel = ∅ := by
  rcases List.mem_cons.mp (List.getLastD_mem_cons (l := w.bodyLabels) (a := ∅)) with heq | hmem
  · exact heq
  · exact h _ hmem

theorem EmptyBodies.not_relaxed {w : LabeledWord} (h : w.EmptyBodies) : w.relaxed = false := by
  simp [relaxed, h.current_empty]

theorem EmptyBodies.read {w v : LabeledWord} {n : ℕ} (h : w.EmptyBodies)
    (hr : w.read ∅ n = some v) : v.EmptyBodies := by
  cases hs : Parser.step w.parser n with
  | none => simp [LabeledWord.read, hs] at hr
  | some p =>
      have heq : w.record ∅ n p = v := by simpa [LabeledWord.read, hs] using hr
      subst v
      cases hp : w.parser with
      | start => simp [EmptyBodies, record, hp]
      | blocks r =>
          cases r with
          | zero => simp [hp, Parser.step] at hs
          | succ r =>
              intro D hD
              have hd : D ∈ w.bodyLabels ∨ D = ∅ := by simpa [record, hp] using hD
              exact hd.elim (h D) id
      | leaves r k => simpa [EmptyBodies, record, hp] using h

end LabeledWord

namespace Macro

theorem first_marker_of_pending {w v : LabeledWord} {xs : List ℕ}
    (hw : w.CursorInvariant) (hstart : w.parser ≠ .start)
    (hbody : w.EmptyBodies) (hp : Pending w)
    (hrun : LabeledWord.advanceRemainder.run w xs = some v) :
    v.markerEvent = true := by
  induction xs generalizing w with
  | nil =>
      have hevent := LabeledWord.advanceRemainder.run_stopped hrun
      have heq : w = v := by
        cases he : w.event with
        | false => simp [ResponseParser.run, LabeledWord.advanceRemainder, he] at hrun
        | true => simpa [ResponseParser.run, LabeledWord.advanceRemainder, he] using hrun
      subst v
      have hnotterm : w.terminal = false := by
        cases ht : w.terminal with
        | false => rfl
        | true => exact (not_pending_terminal hw ht hp).elim
      simpa [LabeledWord.advanceRemainder, LabeledWord.event,
        hnotterm, hbody.not_relaxed] using hevent
  | cons n xs ih =>
      cases he : w.event with
      | true => simp [ResponseParser.run, LabeledWord.advanceRemainder, he] at hrun
      | false =>
          obtain ⟨u, hu⟩ := LabeledWord.read_exists (LabeledWord.event_false_terminal he) ∅ n
          have htail : LabeledWord.advanceRemainder.run u xs = some v := by
            simpa [ResponseParser.run, LabeledWord.advanceRemainder, he, hu] using hrun
          have hlabel := LabeledWord.allowed_empty (LabeledWord.read_nonterminal hu) n
          have hbu := hbody.read hu
          have hmarker : w.markerEvent = false := (Bool.or_eq_false_iff.mp he).2
          have hsize : (∅ : Finset ℕ).card = labelSize 1 w := by
            simp [labelSize, hstart, hmarker]
          have hpu := pending_read (by decide : 0 < 1) hw hp hlabel hu hsize hbu.not_relaxed
          exact ih (hw.read hlabel hu) (LabeledWord.read_parser_ne_start hu) hbu hpu htail

#print axioms first_marker_of_pending

end Macro

namespace Advance

theorem initial_positive_marker (d : ℕ) (hd : 0 < d) (xs : List ℕ) (v : LabeledWord)
    (hinc : xs.Pairwise (· < ·)) (hpos : ∀ x ∈ xs, 0 < x)
    (hrun : parser.run (.prelude ⟨LabeledWord.initial, rfl⟩ d []) xs = some (.remainder v)) :
    v.markerEvent = true := by
  obtain ⟨labels, n, rest, first, last, hxs, hlen, hf, hl, hlast⟩ :=
    run_prelude ⟨LabeledWord.initial, rfl⟩ d [] xs (.remainder v) hrun
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
  have hread : LabeledWord.initial.read labels.toFinset n = some first := by simpa using hf
  have hfirst : first = LabeledCode.rootCursor labels.toFinset n :=
    Option.some.inj (hread.symm.trans (LabeledCode.read_root labels.toFinset n))
  have hlabel : LabeledWord.initial.AllowedLabel labels.toFinset n := ⟨hbound, trivial⟩
  have hcorrect := LabeledWord.cursorInvariant_initial.read hlabel hread
  have hbody : first.EmptyBodies := by
    simp [hfirst, LabeledWord.EmptyBodies, LabeledCode.rootCursor]
  have hpending : Macro.Pending first := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (hcard ▸ hd)
    apply Or.inl
    exact ⟨i, by simpa [hfirst, LabeledCode.rootCursor] using hi,
      by simpa [hfirst, LabeledCode.rootCursor] using (hbound i hi).1⟩
  exact Macro.first_marker_of_pending hcorrect (LabeledWord.read_parser_ne_start hread)
    hbody hpending hl

#print axioms initial_positive_marker

end Advance

end Erdos591.Positive.Game

end Erdos118.Reused591
