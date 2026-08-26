import ErdosProblems.Erdos118.Reused591.LabeledWord

namespace Erdos118.Reused591

/-!
# The fixed-label prelude of an advance response

An advance response first consumes exactly the requested number of label
values and one word coordinate. It then runs the first-event parser.
The finite prelude is included in the well-founded state, so the full
response is a genuine thin finite-input family.
-/

namespace Erdos591.Positive.Game.Advance

abbrev Unfinished := {w : LabeledWord // w.terminal = false}

inductive State where
  | prelude (word : Unfinished) (remaining : ℕ) (labels : List ℕ)
  | remainder (word : LabeledWord)
  deriving Countable

def stopped : State → Bool
  | .prelude _ _ _ => false
  | .remainder w => w.event

def step : State → ℕ → Option State
  | .prelude w 0 labels, n => (w.val.read labels.toFinset n).map State.remainder
  | .prelude w (d + 1) labels, n => some (.prelude w d (labels ++ [n]))
  | .remainder w, n => (w.read ∅ n).map State.remainder

def potential : State → WithTop (ℕ ×ₗ ℕ) ×ₗ ℕ
  | .prelude w d _ => toLex (Parser.potential w.val.parser, d + 1)
  | .remainder w => toLex (Parser.potential w.parser, 0)

theorem step_decreases {s t : State} {n : ℕ} (h : step s n = some t) :
    potential t < potential s := by
  cases s with
  | prelude w d labels =>
      cases d with
      | zero =>
          cases hr : w.val.read labels.toFinset n with
          | none => simp [step, hr] at h
          | some w' =>
              have heq : State.remainder w' = t := by simpa [step, hr] using h
              subst t
              exact Prod.Lex.left _ _ (LabeledWord.read_decreases hr)
      | succ d =>
          have heq : State.prelude w d (labels ++ [n]) = t := by simpa [step] using h
          subst t
          exact Prod.Lex.right _ (Nat.lt_succ_self (d + 1))
  | remainder w =>
      cases hr : w.read ∅ n with
      | none => simp [step, hr] at h
      | some w' =>
          have heq : State.remainder w' = t := by simpa [step, hr] using h
          subst t
          exact Prod.Lex.left _ _ (LabeledWord.read_decreases hr)

theorem step_wellFounded : WellFounded (fun t s => ∃ n, step s n = some t) :=
  (InvImage.wf potential wellFounded_lt).mono fun _ _ h => step_decreases h.choose_spec

theorem live_step (s : State) (hs : stopped s = false) (n : ℕ) :
    ∃ t, step s n = some t := by
  cases s with
  | prelude w d labels =>
      cases d with
      | zero =>
          obtain ⟨w', hw'⟩ := LabeledWord.read_exists w.property labels.toFinset n
          exact ⟨.remainder w', by simp [step, hw']⟩
      | succ d => exact ⟨.prelude w d (labels ++ [n]), rfl⟩
  | remainder w =>
      obtain ⟨w', hw'⟩ := LabeledWord.read_exists
        (LabeledWord.event_false_terminal hs) ∅ n
      exact ⟨.remainder w', by simp [step, hw']⟩

def parser : ResponseParser State :=
  ⟨stopped, step, step_wellFounded, live_step⟩

def responses (w : Unfinished) (d : ℕ) : Set (Finset ℕ) :=
  parser.family (.prelude w d [])

theorem responses_thin (w : Unfinished) (d : ℕ) :
    Erdos590.Larson.NashWilliams.FinThin (responses w d) :=
  parser.family_thin (.prelude w d [])

theorem responses_exist (w : Unfinished) (d : ℕ) {H : Set ℕ} (hH : H.Infinite) :
    ∃ u, u ∈ responses w d ∧ (↑u : Set ℕ) ⊆ H :=
  parser.family_exists (.prelude w d []) hH

theorem responses_nonempty {w : Unfinished} {d : ℕ} {u : Finset ℕ}
    (hu : u ∈ responses w d) : u.Nonempty :=
  parser.family_nonempty rfl hu

theorem run_remainder (w : LabeledWord) (xs : List ℕ) :
    parser.run (.remainder w) xs =
      (LabeledWord.advanceRemainder.run w xs).map State.remainder := by
  induction xs generalizing w with
  | nil =>
      cases he : w.event <;>
        simp [ResponseParser.run, parser, stopped, LabeledWord.advanceRemainder, he]
  | cons n xs ih =>
      cases he : w.event with
      | true => simp [ResponseParser.run, parser, stopped, LabeledWord.advanceRemainder, he]
      | false =>
          cases hr : w.read ∅ n with
          | none =>
              simp [ResponseParser.run, parser, stopped, step, LabeledWord.advanceRemainder, he, hr]
          | some w' =>
              simpa [ResponseParser.run, parser, stopped, step,
                LabeledWord.advanceRemainder, he, hr] using ih w'

/-- Exact decomposition into fresh label values, the first word
coordinate, and the remaining coordinates through the next event. -/
theorem run_prelude (w : Unfinished) (d : ℕ) (acc xs : List ℕ) (q : State)
    (h : parser.run (.prelude w d acc) xs = some q) :
    ∃ labels n rest first last,
      xs = labels ++ n :: rest ∧ labels.length = d ∧
      w.val.read (acc ++ labels).toFinset n = some first ∧
      LabeledWord.advanceRemainder.run first rest = some last ∧
      q = .remainder last := by
  induction d generalizing acc xs with
  | zero =>
      cases xs with
      | nil => simp [ResponseParser.run, parser, stopped] at h
      | cons n xs =>
          obtain ⟨first, hf⟩ := LabeledWord.read_exists w.property acc.toFinset n
          have hr : parser.run (.remainder first) xs = some q := by
            simpa [ResponseParser.run, parser, stopped, step, hf] using h
          rw [run_remainder] at hr
          cases hl : LabeledWord.advanceRemainder.run first xs with
          | none => simp [hl] at hr
          | some last =>
              refine ⟨[], n, xs, first, last, rfl, rfl, ?_, hl, ?_⟩
              · simpa using hf
              · simpa [hl] using hr.symm
  | succ d ih =>
      cases xs with
      | nil => simp [ResponseParser.run, parser, stopped] at h
      | cons x xs =>
          have hr : parser.run (.prelude w d (acc ++ [x])) xs = some q := by
            simpa [ResponseParser.run, parser, stopped, step] using h
          obtain ⟨labels, n, rest, first, last, hxs, hlen, hf, hl, hq⟩ :=
            ih (acc ++ [x]) xs hr
          refine ⟨x :: labels, n, rest, first, last, ?_, by simp [hlen], ?_, hl, hq⟩
          · simp [hxs]
          · simpa only [List.append_assoc, List.singleton_append] using hf

theorem run_result (w : Unfinished) (d : ℕ) (xs : List ℕ) (q : State)
    (h : parser.run (.prelude w d []) xs = some q) :
    ∃ labels n rest last,
      xs = labels ++ n :: rest ∧ labels.length = d ∧ q = .remainder last ∧
      last.coordinates = w.val.coordinates ++ n :: rest ∧
      Parser.potential last.parser < Parser.potential w.val.parser ∧
      last.event = true ∧ (w.val.Parsed → last.Parsed) := by
  obtain ⟨labels, n, rest, first, last, hxs, hlen, hf, hl, hq⟩ :=
    run_prelude w d [] xs q h
  have hf' : w.val.read labels.toFinset n = some first := by simpa using hf
  have hcoords : last.coordinates = first.coordinates ++ rest :=
    LabeledWord.advanceRemainder.run_accumulator LabeledWord.coordinates
      (fun _ _ _ hread => (LabeledWord.read_spec hread).2) hl
  have hle : Parser.potential last.parser ≤ Parser.potential first.parser := by
    apply LabeledWord.advanceRemainder.run_invariant
      (fun u => Parser.potential u.parser ≤ Parser.potential first.parser)
      ?_ (le_refl _) hl
    intro u n v hu huv
    exact (LabeledWord.read_decreases huv).le.trans hu
  refine ⟨labels, n, rest, last, hxs, hlen, hq, ?_,
    hle.trans_lt (LabeledWord.read_decreases hf'),
    LabeledWord.advanceRemainder.run_stopped hl, ?_⟩
  · rw [hcoords, (LabeledWord.read_spec hf').2]
    simp only [List.append_assoc, List.singleton_append]
  · intro hw
    exact (LabeledWord.advanceRemainder_spec (hw.read hf') hl).1

/-- Increasing positive inputs give exactly `d` distinct, positive label
values below the first coordinate. Thus a legal size request produces
legal labels and preserves the cursor invariants. -/
theorem run_invariant (w : Unfinished) (d : ℕ) (xs : List ℕ) (q : State)
    (hw : w.val.CursorInvariant) (hd : w.val.AllowedSize d)
    (hinc : xs.Pairwise (· < ·)) (hpos : ∀ x ∈ xs, 0 < x)
    (h : parser.run (.prelude w d []) xs = some q) :
    ∃ last, q = .remainder last ∧ last.CursorInvariant := by
  obtain ⟨labels, n, rest, first, last, hxs, hlen, hf, hl, hq⟩ :=
    run_prelude w d [] xs q h
  have hp : (labels ++ n :: rest).Pairwise (· < ·) := hxs ▸ hinc
  have hcard : labels.toFinset.card = d :=
    (List.toFinset_card_of_nodup (List.pairwise_append.mp hp).1.nodup).trans hlen
  have hbound : ∀ i ∈ labels.toFinset, 0 < i ∧ i < n := by
    intro i hi
    have hil : i ∈ labels := List.mem_toFinset.mp hi
    refine ⟨hpos i ?_, (List.pairwise_append.mp hp).2.2 i hil n (by simp)⟩
    rw [hxs]
    exact List.mem_append_left _ hil
  have hallowed : w.val.AllowedLabel labels.toFinset n :=
    LabeledWord.allowedLabel_of_size hd hcard hbound
  have hf' : w.val.read labels.toFinset n = some first := by simpa using hf
  exact ⟨last, hq, LabeledWord.advanceRemainder_invariant (hw.read hallowed hf') hl⟩

theorem run_increasing (w : Unfinished) (d : ℕ) (xs : List ℕ) (q : State)
    (hw : w.val.coordinates.Pairwise (· < ·)) (hinc : xs.Pairwise (· < ·))
    (hsep : ∀ x ∈ w.val.coordinates, ∀ y ∈ xs, x < y)
    (h : parser.run (.prelude w d []) xs = some q) :
    ∃ last, q = .remainder last ∧ last.coordinates.Pairwise (· < ·) := by
  obtain ⟨labels, n, rest, last, hxs, _, hq, hcoords, _⟩ := run_result w d xs q h
  have hp : (labels ++ n :: rest).Pairwise (· < ·) := hxs ▸ hinc
  refine ⟨last, hq, ?_⟩
  rw [hcoords]
  refine List.pairwise_append.mpr ⟨hw, (List.pairwise_append.mp hp).2.1, ?_⟩
  intro x hx y hy
  apply hsep x hx y
  rw [hxs]
  exact List.mem_append_right _ hy

#print axioms responses_exist
#print axioms run_prelude
#print axioms run_result
#print axioms run_invariant

end Erdos591.Positive.Game.Advance

end Erdos118.Reused591
