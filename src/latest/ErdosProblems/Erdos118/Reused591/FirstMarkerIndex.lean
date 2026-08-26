import ErdosProblems.Erdos118.Reused591.FirstMarkerResponse

namespace Erdos118.Reused591

/-!
# The first selected-body index is the least root-label entry

Before the opening response stops, every selected root index remains
strictly beyond the number of bodies already read. Reading a selected
marker would require passing a decision event and is therefore excluded
by the actual first-event parser.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

def NoRootPassed (w : LabeledWord) : Prop :=
  ∀ i ∈ w.rootLabel, w.bodyLabels.length < i

theorem NoRootPassed.read {w v : LabeledWord} (h : w.NoRootPassed)
    (hstart : w.parser ≠ .start) (he : w.event = false) {n : ℕ}
    (hr : w.read ∅ n = some v) : v.NoRootPassed := by
  have hm : w.markerEvent = false := (Bool.or_eq_false_iff.mp he).2
  cases hp : w.parser with
  | start => exact (hstart hp).elim
  | blocks r =>
      cases r with
      | zero => simp [LabeledWord.read, hp, Parser.step] at hr
      | succ r =>
          have heq : w.record ∅ n (Parser.normalize r n) = v := by
            simpa [LabeledWord.read, hp, Parser.step] using hr
          subst v
          intro i hi
          have hi' : i ∈ w.rootLabel := by simpa [record, hp] using hi
          have hlt := h i hi'
          have hnot : w.bodyLabels.length + 1 ∉ w.rootLabel := by
            simpa [markerEvent, hp] using hm
          have hne : i ≠ w.bodyLabels.length + 1 := fun heq => hnot (heq ▸ hi')
          simp only [record, hp, List.length_append, List.length_singleton]
          omega
  | leaves r k =>
      have heq : w.record ∅ n (Parser.normalize r k) = v := by
        simpa [LabeledWord.read, hp, Parser.step] using hr
      subst v
      simpa [NoRootPassed, record, hp] using h

theorem NoRootPassed.remainder {w v : LabeledWord} {xs : List ℕ}
    (h : w.NoRootPassed) (hstart : w.parser ≠ .start)
    (hrun : advanceRemainder.run w xs = some v) : v.NoRootPassed := by
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
          exact ih (h.read hstart he hu) (read_parser_ne_start hu) ht

end LabeledWord

namespace Advance

theorem initial_no_root_passed (d : ℕ) (xs : List ℕ) (v : LabeledWord)
    (hpos : ∀ x ∈ xs, 0 < x)
    (hrun : parser.run (.prelude ⟨LabeledWord.initial, rfl⟩ d []) xs = some (.remainder v)) :
    v.NoRootPassed := by
  obtain ⟨labels, n, rest, first, last, hxs, _, hf, hl, hlast⟩ :=
    run_prelude ⟨LabeledWord.initial, rfl⟩ d [] xs (.remainder v) hrun
  have heq : v = last := State.remainder.inj hlast
  subst last
  have hread : LabeledWord.initial.read labels.toFinset n = some first := by simpa using hf
  have hfirst : first = LabeledCode.rootCursor labels.toFinset n :=
    Option.some.inj (hread.symm.trans (LabeledCode.read_root labels.toFinset n))
  have hno : first.NoRootPassed := by
    intro i hi
    have hil : i ∈ labels := by simpa [hfirst, LabeledCode.rootCursor] using hi
    have hip := hpos i (hxs ▸ List.mem_append_left _ hil)
    simpa [hfirst, LabeledCode.rootCursor] using hip
  exact hno.remainder (LabeledWord.read_parser_ne_start hread) hl

theorem initial_first_marker_index (d : ℕ) (hd : 0 < d) (xs : List ℕ) (v : LabeledWord)
    (hinc : xs.Pairwise (· < ·)) (hpos : ∀ x ∈ xs, 0 < x)
    (hrun : parser.run (.prelude ⟨LabeledWord.initial, rfl⟩ d []) xs = some (.remainder v)) :
    v.bodyLabels.length + 1 ∈ v.rootLabel ∧
      ∀ i ∈ v.rootLabel, v.bodyLabels.length + 1 ≤ i := by
  have hm := initial_positive_marker d hd xs v hinc hpos hrun
  have hn := initial_no_root_passed d xs v hpos hrun
  refine ⟨?_, fun i hi => hn i hi⟩
  cases hp : v.parser with
  | start => simp [LabeledWord.markerEvent, hp] at hm
  | leaves r k => simp [LabeledWord.markerEvent, hp] at hm
  | blocks r =>
      cases r with
      | zero => simp [LabeledWord.markerEvent, hp] at hm
      | succ r => simpa [LabeledWord.markerEvent, hp] using hm

#print axioms initial_first_marker_index

end Advance

end Erdos591.Positive.Game

end Erdos118.Reused591
