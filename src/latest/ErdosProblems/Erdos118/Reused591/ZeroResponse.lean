import ErdosProblems.Erdos118.Reused591.ReplyRuns

namespace Erdos118.Reused591

/-!
# Zero-label requests are completion requests

With empty root label there are no selected-body or selected-leaf
events. The first-event remainder parser is therefore exactly the
completion parser. In particular, a zero-size advance from the initial
cursor and a finish request accept precisely the same complete words.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

theorem event_eq_terminal_of_empty_root {w : LabeledWord} (hw : w.rootLabel = ∅) :
    w.event = w.terminal := by
  have hr : w.relaxed = false := by simp [relaxed, hw]
  have hm : w.markerEvent = false := by
    cases hp : w.parser with
    | start => simp [markerEvent, hp]
    | leaves r k => simp [markerEvent, hp]
    | blocks r => cases r <;> simp [markerEvent, hp, hw]
  simp [event, hr, hm]

theorem read_empty_root {w v : LabeledWord} {n : ℕ} (hw : w.rootLabel = ∅)
    (hread : w.read ∅ n = some v) : v.rootLabel = ∅ := by
  by_cases hs : w.parser = .start
  · exact rootLabel_after_read hread (.nil v) hs
  · exact (read_rootLabel_eq hread hs).trans hw

theorem empty_root_parsers {w : LabeledWord} (hw : w.rootLabel = ∅) (xs : List ℕ) :
    advanceRemainder.run w xs = finishParser.run w xs := by
  induction xs generalizing w with
  | nil =>
      simp only [ResponseParser.run, advanceRemainder, finishParser,
        event_eq_terminal_of_empty_root hw]
      rfl
  | cons n xs ih =>
      have he := event_eq_terminal_of_empty_root hw
      cases ht : w.terminal with
      | true => simp [ResponseParser.run, advanceRemainder, finishParser, he, ht]
      | false =>
          cases hr : w.read ∅ n with
          | none => simp [ResponseParser.run, advanceRemainder, finishParser, he, ht, hr]
          | some v =>
              simpa [ResponseParser.run, advanceRemainder, finishParser, he, ht, hr] using
                ih (read_empty_root hw hr)

end LabeledWord

namespace Advance

theorem zero_run_eq_finish (w : Unfinished) (hw : w.val.rootLabel = ∅) (xs : List ℕ) :
    parser.run (.prelude w 0 []) xs =
      (LabeledWord.finishParser.run w.val xs).map State.remainder := by
  cases xs with
  | nil => simp [ResponseParser.run, parser, stopped, LabeledWord.finishParser, w.property]
  | cons n xs =>
      obtain ⟨v, hv⟩ := LabeledWord.read_exists w.property ∅ n
      have hr := LabeledWord.empty_root_parsers (LabeledWord.read_empty_root hw hv) xs
      calc
        _ = parser.run (.remainder v) xs := by
          simp [ResponseParser.run, parser, stopped, step, hv]
        _ = (LabeledWord.advanceRemainder.run v xs).map State.remainder := run_remainder v xs
        _ = (LabeledWord.finishParser.run w.val (n :: xs)).map State.remainder := by
          rw [hr]
          simp [ResponseParser.run, LabeledWord.finishParser, w.property, hv]

end Advance

theorem Reply.zero_advance_iff_finish (board : Board) (side : Bool) (u : Finset ℕ)
    (last : Board) (hroot : (board.get side).rootLabel = ∅) :
    Reply board ⟨side, .advance 0⟩ u last ↔ Reply board ⟨side, .finish⟩ u last := by
  constructor
  · intro h
    cases h with
    | advance side d u w hlegal hrun =>
        rw [Advance.zero_run_eq_finish ⟨board.get side, hlegal.1⟩ hroot] at hrun
        cases hf : LabeledWord.finishParser.run (board.get side) (u.sort (· ≤ ·)) with
        | none => simp [hf] at hrun
        | some v =>
            have heq : v = w := by simpa [hf] using hrun
            subst v
            exact .finish side u w hlegal.1 hf
  · intro h
    cases h with
    | finish side u w hlegal hrun =>
        have hr := Advance.zero_run_eq_finish ⟨board.get side, hlegal⟩ hroot (u.sort (· ≤ ·))
        rw [hrun] at hr
        exact .advance side 0 u w ⟨hlegal, Or.inl rfl⟩ hr

theorem Reply.size_zero_iff_finish (board : Board) (r : Request) (u : Finset ℕ)
    (last : Board) (hroot : (board.get r.side).rootLabel = ∅) (hsize : r.size = 0) :
    Reply board r u last ↔ Reply board ⟨r.side, .finish⟩ u last := by
  cases r with
  | mk side command =>
      cases command with
      | finish => rfl
      | advance d =>
          have hd : d = 0 := hsize
          subst d
          exact Reply.zero_advance_iff_finish board side u last hroot

theorem Reply.finish_terminal {board last : Board} {side : Bool} {u : Finset ℕ}
    (h : Reply board ⟨side, .finish⟩ u last) : (last.get side).terminal = true := by
  cases h with
  | finish side u w _ hr =>
      simpa [LabeledWord.finishParser] using LabeledWord.finishParser.run_stopped hr

theorem Reply.size_zero_terminal {board last : Board} {r : Request} {u : Finset ℕ}
    (h : Reply board r u last) (hroot : (board.get r.side).rootLabel = ∅)
    (hsize : r.size = 0) : (last.get r.side).terminal = true :=
  ((Reply.size_zero_iff_finish board r u last hroot hsize).mp h).finish_terminal

#print axioms Advance.zero_run_eq_finish
#print axioms Reply.zero_advance_iff_finish

end Erdos591.Positive.Game

end Erdos118.Reused591
