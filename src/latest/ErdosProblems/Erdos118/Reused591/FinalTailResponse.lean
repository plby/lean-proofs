import ErdosProblems.Erdos118.Reused591.MacroPending
import ErdosProblems.Erdos118.Reused591.ZeroResponse

namespace Erdos118.Reused591

/-!
# Commands after the last selected leaf

Once the root is fixed and no selected body or leaf remains unread,
every legal command has size zero. Its first read is followed by no
decision event before completion, so either command accepts precisely
the complete tail. This also applies when the starting cursor itself
is relaxed: the advance prelude consumes a new coordinate first.
-/

namespace Erdos591.Positive.Game

namespace Macro

theorem marker_pending {w : LabeledWord} (hm : w.markerEvent = true) : Pending w := by
  cases hp : w.parser with
  | start => simp [LabeledWord.markerEvent, hp] at hm
  | leaves r k => simp [LabeledWord.markerEvent, hp] at hm
  | blocks r =>
      cases r with
      | zero => simp [LabeledWord.markerEvent, hp] at hm
      | succ r =>
          have hs : w.bodyLabels.length + 1 ∈ w.rootLabel := by
            simpa [LabeledWord.markerEvent, hp] using hm
          exact Or.inl ⟨_, hs, Nat.lt_succ_self _⟩

theorem no_pending_read {w v : LabeledWord} (hw : w.parser ≠ .start) (hp : ¬ Pending w)
    {D : Finset ℕ} {n : ℕ} (hread : w.read D n = some v) :
    ¬ Pending v ∧ v.relaxed = false := by
  refine ⟨fun h => hp (pending_before_read hw hread (Or.inl h)), ?_⟩
  cases hr : v.relaxed with
  | false => rfl
  | true => exact (hp (pending_before_read hw hread (Or.inr hr))).elim

theorem event_eq_terminal {w : LabeledWord} (hp : ¬ Pending w) (hr : w.relaxed = false) :
    w.event = w.terminal := by
  have hm : w.markerEvent = false := by
    cases hh : w.markerEvent with
    | false => rfl
    | true => exact (hp (marker_pending hh)).elim
  simp [LabeledWord.event, hr, hm]

theorem remainder_eq_finish {w : LabeledWord} (hw : w.parser ≠ .start)
    (hp : ¬ Pending w) (hr : w.relaxed = false) (xs : List ℕ) :
    LabeledWord.advanceRemainder.run w xs = LabeledWord.finishParser.run w xs := by
  induction xs generalizing w with
  | nil =>
      simp only [ResponseParser.run, LabeledWord.advanceRemainder, LabeledWord.finishParser,
        event_eq_terminal hp hr]
      rfl
  | cons n xs ih =>
      have he := event_eq_terminal hp hr
      cases ht : w.terminal with
      | true =>
          simp [ResponseParser.run, LabeledWord.advanceRemainder, LabeledWord.finishParser, he, ht]
      | false =>
          obtain ⟨v, hv⟩ := LabeledWord.read_exists ht ∅ n
          have hnv := no_pending_read hw hp hv
          simpa [ResponseParser.run, LabeledWord.advanceRemainder, LabeledWord.finishParser,
            he, ht, hv] using ih (LabeledWord.read_parser_ne_start hv) hnv.1 hnv.2

end Macro

namespace Advance

theorem zero_run_eq_finish_of_not_pending (w : Unfinished) (hw : w.val.parser ≠ .start)
    (hp : ¬ Macro.Pending w.val) (xs : List ℕ) :
    parser.run (.prelude w 0 []) xs =
      (LabeledWord.finishParser.run w.val xs).map State.remainder := by
  cases xs with
  | nil => simp [ResponseParser.run, parser, stopped, LabeledWord.finishParser, w.property]
  | cons n xs =>
      obtain ⟨v, hv⟩ := LabeledWord.read_exists w.property ∅ n
      have hnv := Macro.no_pending_read hw hp hv
      have hr := Macro.remainder_eq_finish (LabeledWord.read_parser_ne_start hv) hnv.1 hnv.2 xs
      calc
        _ = parser.run (.remainder v) xs := by
          simp [ResponseParser.run, parser, stopped, step, hv]
        _ = (LabeledWord.advanceRemainder.run v xs).map State.remainder := run_remainder v xs
        _ = (LabeledWord.finishParser.run w.val (n :: xs)).map State.remainder := by
          rw [hr]
          simp [ResponseParser.run, LabeledWord.finishParser, w.property, hv]

end Advance

theorem Request.Legal.size_zero_of_not_pending {board : Board} {r : Request}
    (hlegal : r.Legal board) (hw : (board.get r.side).parser ≠ .start)
    (hp : ¬ Macro.Pending (board.get r.side)) : r.size = 0 := by
  cases hc : r.command with
  | finish => simp [Request.size, hc]
  | advance d =>
      have hd : (board.get r.side).AllowedSize d := by simpa [Request.Legal, hc] using hlegal
      rcases hd.2 with hd | hs | hm
      · simpa [Request.size, hc] using hd
      · exact (hw hs).elim
      · exact (hp (Macro.marker_pending hm)).elim

theorem Reply.not_pending_iff_finish (board : Board) (r : Request) (u : Finset ℕ)
    (last : Board) (hlegal : r.Legal board) (hw : (board.get r.side).parser ≠ .start)
    (hp : ¬ Macro.Pending (board.get r.side)) :
    Reply board r u last ↔ Reply board ⟨r.side, .finish⟩ u last := by
  have hsize := hlegal.size_zero_of_not_pending hw hp
  cases r with
  | mk side command =>
      cases command with
      | finish => rfl
      | advance d =>
          have hd : d = 0 := hsize
          subst d
          constructor
          · intro h
            cases h with
            | advance side d u w hlegal hrun =>
                rw [Advance.zero_run_eq_finish_of_not_pending
                  ⟨board.get side, hlegal.1⟩ hw hp] at hrun
                cases hf : LabeledWord.finishParser.run (board.get side) (u.sort (· ≤ ·)) with
                | none => simp [hf] at hrun
                | some v =>
                    have heq : v = w := by simpa [hf] using hrun
                    subst v
                    exact .finish side u w hlegal.1 hf
          · intro h
            cases h with
            | finish side u w hlegal hrun =>
                have hr := Advance.zero_run_eq_finish_of_not_pending
                  ⟨board.get side, hlegal⟩ hw hp (u.sort (· ≤ ·))
                rw [hrun] at hr
                exact .advance side 0 u w ⟨hlegal, Or.inl rfl⟩ hr

#print axioms Advance.zero_run_eq_finish_of_not_pending
#print axioms Request.Legal.size_zero_of_not_pending
#print axioms Reply.not_pending_iff_finish

end Erdos591.Positive.Game

end Erdos118.Reused591
