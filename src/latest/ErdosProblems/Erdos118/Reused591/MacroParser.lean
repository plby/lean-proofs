import ErdosProblems.Erdos118.Reused591.AdvanceResponse

namespace Erdos118.Reused591

/-!
# Uninterrupted macro-extensions for the builder family

A fixed size `q` is used at every newly read root or selected body
marker. Administrative marker events do not stop this construction:
the next label prelude begins on the same word immediately. The macro
stops only at its first new selected leaf or at word completion.
-/

namespace Erdos591.Positive.Game.Macro

abbrev Unfinished := Advance.Unfinished

def labelSize (q : ℕ) (w : LabeledWord) : ℕ :=
  if w.parser = .start ∨ w.markerEvent = true then q else 0

theorem labelSize_le (q : ℕ) (w : LabeledWord) : labelSize q w ≤ q := by
  unfold labelSize
  split <;> omega

theorem labelSize_allowed (q : ℕ) (w : Unfinished) :
    w.val.AllowedSize (labelSize q w.val) := by
  refine ⟨w.property, ?_⟩
  unfold labelSize
  split
  · exact Or.inr ‹w.val.parser = .start ∨ w.val.markerEvent = true›
  · exact Or.inl rfl

inductive State where
  | prelude (word : Unfinished) (remaining : ℕ) (labels : List ℕ)
  | done (word : LabeledWord)
  deriving Countable

def word : State → LabeledWord
  | .prelude w _ _ => w.val
  | .done w => w

def stopped : State → Bool
  | .prelude _ _ _ => false
  | .done _ => true

def resume (q : ℕ) (w : LabeledWord) : State :=
  if h : w.terminal = true ∨ w.relaxed = true then .done w
  else .prelude ⟨w, by cases ht : w.terminal <;> simp_all⟩ (labelSize q w) []

@[simp] theorem word_resume (q : ℕ) (w : LabeledWord) : word (resume q w) = w := by
  unfold resume
  split <;> rfl

def step (q : ℕ) : State → ℕ → Option State
  | .prelude w 0 labels, n => (w.val.read labels.toFinset n).map (resume q)
  | .prelude w (d + 1) labels, n => some (.prelude w d (labels ++ [n]))
  | .done _, _ => none

def potential : State → WithTop (ℕ ×ₗ ℕ) ×ₗ ℕ
  | .prelude w d _ => toLex (Parser.potential w.val.parser, d + 1)
  | .done w => toLex (Parser.potential w.parser, 0)

theorem resume_lt_prelude (q : ℕ) (w : Unfinished) (d : ℕ) (labels : List ℕ)
    (v : LabeledWord) (hv : Parser.potential v.parser < Parser.potential w.val.parser) :
    potential (resume q v) < potential (.prelude w d labels) := by
  unfold resume
  split <;> exact Prod.Lex.left _ _ hv

theorem step_decreases (q : ℕ) {s t : State} {n : ℕ} (h : step q s n = some t) :
    potential t < potential s := by
  cases s with
  | done w => simp [step] at h
  | prelude w d labels =>
      cases d with
      | zero =>
          cases hr : w.val.read labels.toFinset n with
          | none => simp [step, hr] at h
          | some v =>
              have heq : resume q v = t := by simpa [step, hr] using h
              subst t
              exact resume_lt_prelude q w 0 labels v (LabeledWord.read_decreases hr)
      | succ d =>
          have heq : State.prelude w d (labels ++ [n]) = t := by simpa [step] using h
          subst t
          exact Prod.Lex.right _ (Nat.lt_succ_self (d + 1))

theorem step_wellFounded (q : ℕ) : WellFounded (fun t s => ∃ n, step q s n = some t) :=
  (InvImage.wf potential wellFounded_lt).mono fun _ _ h => step_decreases q h.choose_spec

theorem live_step (q : ℕ) (s : State) (hs : stopped s = false) (n : ℕ) :
    ∃ t, step q s n = some t := by
  cases s with
  | done w => simp [stopped] at hs
  | prelude w d labels =>
      cases d with
      | zero =>
          obtain ⟨v, hv⟩ := LabeledWord.read_exists w.property labels.toFinset n
          exact ⟨resume q v, by simp [step, hv]⟩
      | succ d => exact ⟨.prelude w d (labels ++ [n]), rfl⟩

def parser (q : ℕ) : ResponseParser State :=
  ⟨stopped, step q, step_wellFounded q, live_step q⟩

def start (q : ℕ) (w : Unfinished) : State := .prelude w (labelSize q w.val) []

def responses (q : ℕ) (w : Unfinished) : Set (Finset ℕ) := (parser q).family (start q w)

theorem responses_exist (q : ℕ) (w : Unfinished) {H : Set ℕ} (hH : H.Infinite) :
    ∃ u, u ∈ responses q w ∧ (↑u : Set ℕ) ⊆ H :=
  (parser q).family_exists (start q w) hH

theorem responses_nonempty (q : ℕ) (w : Unfinished) {u : Finset ℕ}
    (hu : u ∈ responses q w) : u.Nonempty :=
  (parser q).family_nonempty rfl hu

def EndValid : State → Prop
  | .prelude _ _ _ => True
  | .done w => w.terminal = true ∨ w.relaxed = true

theorem endValid_resume (q : ℕ) (w : LabeledWord) : EndValid (resume q w) := by
  unfold resume
  split
  · exact ‹w.terminal = true ∨ w.relaxed = true›
  · trivial

theorem endValid_step (q : ℕ) {s t : State} {n : ℕ} (h : step q s n = some t) :
    EndValid t := by
  cases s with
  | done w => simp [step] at h
  | prelude w d labels =>
      cases d with
      | zero =>
          cases hr : w.val.read labels.toFinset n with
          | none => simp [step, hr] at h
          | some v =>
              have heq : resume q v = t := by simpa [step, hr] using h
              exact heq ▸ endValid_resume q v
      | succ d =>
          have heq : State.prelude w d (labels ++ [n]) = t := by simpa [step] using h
          exact heq ▸ trivial

theorem run_end (q : ℕ) (w : Unfinished) (d : ℕ) (acc xs : List ℕ) (t : State)
    (h : (parser q).run (.prelude w d acc) xs = some t) :
    ∃ v, t = .done v ∧ (v.terminal = true ∨ v.relaxed = true) := by
  have hs := (parser q).run_stopped h
  have hv := (parser q).run_invariant EndValid
    (fun _ _ _ _ hh => endValid_step q hh) (show EndValid (.prelude w d acc) from trivial) h
  cases t with
  | prelude _ _ _ => simp [parser, stopped] at hs
  | done v => exact ⟨v, rfl, hv⟩

/-- Split the fixed first label prelude from the remaining macro input.
After its coordinate, the macro resumes on the same word. -/
theorem run_prelude (q : ℕ) (w : Unfinished) (d : ℕ) (acc xs : List ℕ) (t : State)
    (h : (parser q).run (.prelude w d acc) xs = some t) :
    ∃ labels n rest v,
      xs = labels ++ n :: rest ∧ labels.length = d ∧
      w.val.read (acc ++ labels).toFinset n = some v ∧
      (parser q).run (resume q v) rest = some t := by
  induction d generalizing acc xs with
  | zero =>
      cases xs with
      | nil => simp [ResponseParser.run, parser, stopped] at h
      | cons n xs =>
          obtain ⟨v, hv⟩ := LabeledWord.read_exists w.property acc.toFinset n
          refine ⟨[], n, xs, v, rfl, rfl, by simpa using hv, ?_⟩
          simpa [ResponseParser.run, parser, stopped, step, hv] using h
  | succ d ih =>
      cases xs with
      | nil => simp [ResponseParser.run, parser, stopped] at h
      | cons n xs =>
          have ht : (parser q).run (.prelude w d (acc ++ [n])) xs = some t := by
            simpa [ResponseParser.run, parser, stopped, step] using h
          obtain ⟨labels, m, rest, v, hxs, hlen, hv, hr⟩ := ih (acc ++ [n]) xs ht
          refine ⟨n :: labels, m, rest, v, by simp [hxs], by simp [hlen], ?_, hr⟩
          simpa only [List.append_assoc, List.singleton_append] using hv

#print axioms responses_exist
#print axioms run_end
#print axioms run_prelude

end Erdos591.Positive.Game.Macro

end Erdos118.Reused591
