import ErdosProblems.Erdos591.FirstMarkerIndex

/-!
# An advance response cannot skip an unread selected body

The target body index stays in the fixed root label and strictly above
the number of body markers read. Only the first coordinate of an advance
response can cross that index, and only if the request was already at
its selected marker. The first-event remainder cannot cross it.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

def BeforeBody (i : ℕ) (w : LabeledWord) : Prop :=
  i ∈ w.rootLabel ∧ w.bodyLabels.length < i

theorem BeforeBody.read_away {i : ℕ} {w v : LabeledWord} {D : Finset ℕ} {n : ℕ}
    (h : BeforeBody i w) (hstart : w.parser ≠ .start)
    (hnot : ¬ (w.markerEvent = true ∧ w.bodyLabels.length + 1 = i))
    (hr : w.read D n = some v) : BeforeBody i v := by
  cases hp : w.parser with
  | start => exact (hstart hp).elim
  | blocks r =>
      cases r with
      | zero => simp [LabeledWord.read, hp, Parser.step] at hr
      | succ r =>
          have hneq : w.bodyLabels.length + 1 ≠ i := by
            intro heq
            apply hnot
            exact ⟨by simpa [markerEvent, hp, heq] using h.1, heq⟩
          have heq : w.record D n (Parser.normalize r n) = v := by
            simpa [LabeledWord.read, hp, Parser.step] using hr
          subst v
          refine ⟨by simpa [record, hp] using h.1, ?_⟩
          simp only [record, hp, List.length_append, List.length_singleton]
          have hlt := h.2
          omega
  | leaves r k =>
      have heq : w.record D n (Parser.normalize r k) = v := by
        simpa [LabeledWord.read, hp, Parser.step] using hr
      subst v
      simpa [BeforeBody, record, hp] using h

theorem BeforeBody.remainder {i : ℕ} {w v : LabeledWord} {xs : List ℕ}
    (h : BeforeBody i w) (hstart : w.parser ≠ .start)
    (hr : advanceRemainder.run w xs = some v) : BeforeBody i v := by
  induction xs generalizing w with
  | nil =>
      cases he : w.event with
      | false => simp [ResponseParser.run, advanceRemainder, he] at hr
      | true =>
          have heq : w = v := by simpa [ResponseParser.run, advanceRemainder, he] using hr
          exact heq ▸ h
  | cons n xs ih =>
      cases he : w.event with
      | true => simp [ResponseParser.run, advanceRemainder, he] at hr
      | false =>
          obtain ⟨u, hu⟩ := read_exists (event_false_terminal he) ∅ n
          have ht : advanceRemainder.run u xs = some v := by
            simpa [ResponseParser.run, advanceRemainder, he, hu] using hr
          have hnot : ¬ (w.markerEvent = true ∧ w.bodyLabels.length + 1 = i) := by
            rintro ⟨hm, _⟩
            simp [event, hm] at he
          exact ih (h.read_away hstart hnot hu) (read_parser_ne_start hu) ht

theorem BeforeBody.not_terminal {i : ℕ} {w : LabeledWord}
    (h : BeforeBody i w) (hw : w.CursorInvariant) : w.terminal = false := by
  cases ht : w.terminal with
  | false => rfl
  | true =>
      have hp : w.parser = .blocks 0 := by simpa [terminal] using ht
      have hc := hw.2.1.1
      simp only [hp, outstandingBodies, Nat.add_zero] at hc
      have hi := (hw.2.2.1 i h.1).2
      have hlt := h.2
      omega

end LabeledWord

namespace Advance

theorem before_body_or_marker (w : Unfinished) (d : ℕ) (xs : List ℕ) (v : LabeledWord)
    {i : ℕ} (h : LabeledWord.BeforeBody i w.val) (hstart : w.val.parser ≠ .start)
    (hr : parser.run (.prelude w d []) xs = some (.remainder v)) :
    LabeledWord.BeforeBody i v ∨ (w.val.markerEvent = true ∧ w.val.bodyLabels.length + 1 = i) := by
  by_cases hm : w.val.markerEvent = true ∧ w.val.bodyLabels.length + 1 = i
  · exact Or.inr hm
  obtain ⟨labels, n, rest, first, last, _, _, hf, hl, hlast⟩ :=
    run_prelude w d [] xs (.remainder v) hr
  have heq : v = last := State.remainder.inj hlast
  subst last
  have hread : w.val.read labels.toFinset n = some first := by simpa using hf
  exact Or.inl ((h.read_away hstart hm hread).remainder
    (LabeledWord.read_parser_ne_start hread) hl)

#print axioms before_body_or_marker

end Advance

theorem Reply.advance_before_body_or_marker {board last : Board} {side : Bool}
    {d i : ℕ} {u : Finset ℕ} (hr : Reply board ⟨side, .advance d⟩ u last)
    (h : LabeledWord.BeforeBody i (board.get side))
    (hstart : (board.get side).parser ≠ .start) :
    LabeledWord.BeforeBody i (last.get side) ∨
      ((board.get side).markerEvent = true ∧ (board.get side).bodyLabels.length + 1 = i) := by
  cases hr with
  | advance side d u v hlegal hrun =>
      simpa using Advance.before_body_or_marker ⟨board.get side, hlegal.1⟩ d
        (u.sort (· ≤ ·)) v h hstart hrun

end Erdos591.Positive.Game
