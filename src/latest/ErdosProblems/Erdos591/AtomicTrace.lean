import ErdosProblems.Erdos591.GameClosed

/-!
# Atomic coordinate traces and their response decomposition

An atom contains one word coordinate and its preceding finite label.
The trace records actual legal cursor reads. A switch to the other word
is allowed only after an event. A completed trace is split into the
same first-event responses used by the game; no alternative parser or
terminal language is introduced.
-/

namespace Erdos591.Positive.Game

namespace Board

@[simp] theorem get_update (b : Board) (side : Bool) (w : LabeledWord) :
    (b.update side w).get side = w := by cases side <;> rfl

@[simp] theorem update_get (b : Board) (side : Bool) : b.update side (b.get side) = b := by
  cases side <;> rfl

@[simp] theorem update_update (b : Board) (side : Bool) (w v : LabeledWord) :
    (b.update side w).update side v = b.update side v := by cases side <;> rfl

theorem terminal_of_done {b : Board} (hb : Concrete.done b = true) (side : Bool) :
    (b.get side).terminal = true := by
  have h : b.left.terminal = true ∧ b.right.terminal = true := by
    simpa [Concrete.done] using hb
  cases side
  · exact h.1
  · exact h.2

theorem not_done_of_live {b : Board} {side : Bool}
    (hb : (b.get side).terminal = false) : Concrete.done b = false := by
  cases hd : Concrete.done b with
  | false => rfl
  | true =>
      have ht := b.terminal_of_done hd side
      simp [hb] at ht

end Board

namespace LabeledWord

theorem read_parser_ne_start {w w' : LabeledWord} {D : Finset ℕ} {n : ℕ}
    (h : w.read D n = some w') : w'.parser ≠ .start := by
  have hs := (read_spec h).1
  cases hp : w.parser with
  | start =>
      intro heq
      simp [hp, heq, Parser.step] at hs
  | blocks r =>
      cases r with
      | zero => simp [hp, Parser.step] at hs
      | succ r =>
          have heq : w'.parser = Parser.normalize r n := by
            simpa [hp, Parser.step] using hs.symm
          cases n <;> simp [heq, Parser.normalize]
  | leaves r k =>
      have heq : w'.parser = Parser.normalize r k := by
        simpa [hp, Parser.step] using hs.symm
      cases k <;> simp [heq, Parser.normalize]

theorem allowedSize_of_label {w w' : LabeledWord} {D : Finset ℕ} {n : ℕ}
    (hD : w.AllowedLabel D n) (hr : w.read D n = some w') : w.AllowedSize D.card := by
  refine ⟨read_nonterminal hr, ?_⟩
  by_cases hzero : D = ∅
  · exact Or.inl (by simp [hzero])
  · right
    cases hp : w.parser with
    | start => exact Or.inl rfl
    | leaves r k => exact (hzero (by simpa [AllowedLabel, hp] using hD.2)).elim
    | blocks r =>
        cases r with
        | zero => simp [LabeledWord.read, hp, Parser.step] at hr
        | succ r =>
            right
            have hsel : w.bodyLabels.length + 1 ∈ w.rootLabel := by
              by_contra hn
              have hd : w.bodyLabels.length + 1 ∉ w.rootLabel → D = ∅ := by
                simpa [hp] using hD.2
              exact hzero (hd hn)
            simpa [markerEvent, hp] using hsel

theorem label_empty_of_no_event {w : LabeledWord} {D : Finset ℕ} {n : ℕ}
    (hD : w.AllowedLabel D n) (hs : w.parser ≠ .start) (he : w.event = false) : D = ∅ := by
  have hm : w.markerEvent = false := (Bool.or_eq_false_iff.mp he).2
  cases hp : w.parser with
  | start => exact (hs hp).elim
  | leaves r k => simpa [hp] using hD.2
  | blocks r =>
      cases r with
      | zero => simpa [hp] using hD.2
      | succ r =>
          have hd : w.bodyLabels.length + 1 ∉ w.rootLabel → D = ∅ := by
            simpa [hp] using hD.2
          apply hd
          simpa [markerEvent, hp] using hm

end LabeledWord

namespace Advance

theorem run_prelude_build (w : Unfinished) (acc labels : List ℕ) (n : ℕ)
    (rest : List ℕ) (first last : LabeledWord)
    (hf : w.val.read (acc ++ labels).toFinset n = some first)
    (hl : LabeledWord.advanceRemainder.run first rest = some last) :
    parser.run (.prelude w labels.length acc) (labels ++ n :: rest) =
      some (.remainder last) := by
  induction labels generalizing acc with
  | nil =>
      have hf' : w.val.read acc.toFinset n = some first := by simpa using hf
      have hrun := (run_remainder first rest).trans
        (congrArg (Option.map State.remainder) hl)
      simpa [ResponseParser.run, parser, stopped, step, hf'] using hrun
  | cons x xs ih =>
      have hread : w.val.read ((acc ++ [x]) ++ xs).toFinset n = some first := by
        simpa [List.append_assoc] using hf
      simpa [ResponseParser.run, parser, stopped, step] using ih (acc ++ [x]) hread

end Advance

namespace Atomic

structure Atom where
  side : Bool
  label : Finset ℕ
  value : ℕ
  deriving DecidableEq, Countable

def Atom.inputs (a : Atom) : List ℕ := a.label.sort (· ≤ ·) ++ [a.value]

def inputs (xs : List Atom) : List ℕ := xs.flatMap Atom.inputs

@[simp] theorem inputs_nil : inputs [] = [] := rfl

@[simp] theorem inputs_cons (a : Atom) (xs : List Atom) :
    inputs (a :: xs) = a.inputs ++ inputs xs := List.flatMap_cons

@[simp] theorem inputs_append (xs ys : List Atom) :
    inputs (xs ++ ys) = inputs xs ++ inputs ys := List.flatMap_append

theorem Atom.value_mem (a : Atom) : a.value ∈ a.inputs := by simp [Atom.inputs]

theorem Atom.inputs_ne_nil (a : Atom) : a.inputs ≠ [] := by simp [Atom.inputs]

/-- The next atom stays on this side unless the current cursor is at an event. -/
def Ready (b : Board) (side : Bool) (xs : List Atom) : Prop :=
  ∀ a ∈ xs.head?, (b.get side).event = false → a.side = side

/-- A faithful elementary execution. Numerical separation and membership
in the conservative pool are imposed on the flattened input separately. -/
inductive Trace : Board → List Atom → Board → Prop
  | nil (b : Board) : Trace b [] b
  | cons (b : Board) (a : Atom) (w : LabeledWord) (xs : List Atom) (last : Board)
      (hlabel : (b.get a.side).AllowedLabel a.label a.value)
      (hread : (b.get a.side).read a.label a.value = some w)
      (hready : Ready (b.update a.side w) a.side xs)
      (htail : Trace (b.update a.side w) xs last) : Trace b (a :: xs) last

/-- Stop a trace at the first decision event. All intervening labels
are necessarily empty, and all intervening atoms stay on the same side. -/
theorem remainder_split {b last : Board} {xs : List Atom} (ht : Trace b xs last)
    (hdone : Concrete.done last = true) (side : Bool)
    (hstart : (b.get side).parser ≠ .start) (hready : Ready b side xs) :
    ∃ front tail w,
      xs = front ++ tail ∧ inputs front = front.map Atom.value ∧
      LabeledWord.advanceRemainder.run (b.get side) (front.map Atom.value) = some w ∧
      Trace (b.update side w) tail last := by
  induction ht with
  | nil b =>
      have he : (b.get side).event = true := by
        simp [LabeledWord.event, b.terminal_of_done hdone side]
      refine ⟨[], [], b.get side, rfl, rfl, ?_, ?_⟩
      · simp [ResponseParser.run, LabeledWord.advanceRemainder, he]
      · simpa using Trace.nil b
  | cons b a w xs last hlabel hread htailready htail ih =>
      cases he : (b.get side).event with
      | true =>
          refine ⟨[], a :: xs, b.get side, rfl, rfl, ?_, ?_⟩
          · simp [ResponseParser.run, LabeledWord.advanceRemainder, he]
          · simpa using Trace.cons b a w xs last hlabel hread htailready htail
      | false =>
          have hside : a.side = side := hready a (by simp) he
          have hlabel' : (b.get side).AllowedLabel a.label a.value := hside ▸ hlabel
          have hread' : (b.get side).read a.label a.value = some w := hside ▸ hread
          have hempty : a.label = ∅ :=
            LabeledWord.label_empty_of_no_event hlabel' hstart he
          obtain ⟨front, tail, v, hxs, hi, hr, ht⟩ := ih hdone
            (by simpa [hside] using LabeledWord.read_parser_ne_start hread')
            (by simpa [hside] using htailready)
          refine ⟨a :: front, tail, v, by simp [hxs], ?_, ?_, ?_⟩
          · simp [hempty, Atom.inputs, hi]
          · have hr' : LabeledWord.advanceRemainder.run w (front.map Atom.value) =
                some v := by simpa [hside] using hr
            simpa [ResponseParser.run, LabeledWord.advanceRemainder, he,
              ← hempty, hread'] using hr'
          · simpa [hside] using ht

/-- The first atom and the subsequent empty-label atoms through the
first event form one actual advance response. -/
theorem response_split {b last : Board} {a : Atom} {xs : List Atom}
    (ht : Trace b (a :: xs) last) (hdone : Concrete.done last = true)
    (hinc : (inputs (a :: xs)).Pairwise (· < ·)) :
    ∃ middle tail w,
      xs = middle ++ tail ∧ inputs middle = middle.map Atom.value ∧
      Reply b ⟨a.side, .advance a.label.card⟩
        (inputs (a :: middle)).toFinset (b.update a.side w) ∧
      Trace (b.update a.side w) tail last := by
  cases ht with
  | cons b a w xs last hlabel hread hready htail =>
      obtain ⟨middle, tail, v, hxs, hi, hr, ht⟩ :=
        remainder_split htail hdone a.side
          (by simpa using LabeledWord.read_parser_ne_start hread) hready
      have hr' : LabeledWord.advanceRemainder.run w (middle.map Atom.value) = some v := by
        simpa using hr
      have hlegal := LabeledWord.allowedSize_of_label hlabel hread
      have hread' : (b.get a.side).read
          ([] ++ a.label.sort (· ≤ ·)).toFinset a.value = some w := by
        simpa using hread
      have hrun := Advance.run_prelude_build ⟨b.get a.side, hlegal.1⟩ []
        (a.label.sort (· ≤ ·)) a.value (middle.map Atom.value) w v hread' hr'
      have hpair : (inputs (a :: middle) ++ inputs tail).Pairwise (· < ·) := by
        simpa [hxs, List.append_assoc] using hinc
      refine ⟨middle, tail, v, hxs, hi, ?_, by simpa using ht⟩
      apply Reply.advance a.side a.label.card (inputs (a :: middle)).toFinset v hlegal
      rw [Erdos590.Larson.sort_toFinset_eq_self_of_pairwise
        (List.pairwise_append.mp hpair).1]
      simpa [Atom.inputs, hi] using hrun

#print axioms remainder_split
#print axioms response_split

end Atomic

end Erdos591.Positive.Game
