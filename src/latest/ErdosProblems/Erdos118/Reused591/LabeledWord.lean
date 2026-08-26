import ErdosProblems.Erdos118.Reused591.GameParser
import ErdosProblems.Erdos118.Reused591.ResponseParser
import Mathlib.Tactic.DeriveCountable

namespace Erdos118.Reused591

/-!
# Labeled height-two word cursors

The root and body labels use the one-based successor indices of the
mathematical game. The cursor records actual word coordinates separately
from these labels. `read` is the structural transition; `AllowedLabel`
records the label legality condition, to be imposed together with global
freshness by the game histories.
-/

namespace Erdos591.Positive.Game

deriving instance Countable for Parser.State

structure LabeledWord where
  parser : Parser.State
  coordinates : List ℕ
  rootLabel : Finset ℕ
  bodyLabels : List (Finset ℕ)
  leafIndex : ℕ
  rootMarker : ℕ
  bodyMarker : ℕ
  deriving DecidableEq, Countable

namespace LabeledWord

def initial : LabeledWord := ⟨.start, [], ∅, [], 0, 0, 0⟩

def terminal (w : LabeledWord) : Bool := decide (w.parser = .blocks 0)

def currentLabel (w : LabeledWord) : Finset ℕ := w.bodyLabels.getLastD ∅

/-- This cursor ends immediately after a selected leaf. -/
def relaxed (w : LabeledWord) : Bool :=
  decide (0 < w.leafIndex ∧ w.bodyLabels.length ∈ w.rootLabel ∧
    w.leafIndex ∈ w.currentLabel)

/-- The next coordinate is the marker of a selected body; its label has
not yet been read. -/
def markerEvent (w : LabeledWord) : Bool :=
  match w.parser with
  | .blocks (_ + 1) => decide (w.bodyLabels.length + 1 ∈ w.rootLabel)
  | _ => false

def event (w : LabeledWord) : Bool := w.terminal || w.relaxed || w.markerEvent

/-- The structural update after consuming one word coordinate. -/
def record (w : LabeledWord) (L : Finset ℕ) (n : ℕ) (s : Parser.State) : LabeledWord :=
  { parser := s
    coordinates := w.coordinates ++ [n]
    rootLabel := match w.parser with
      | .start => L
      | _ => w.rootLabel
    bodyLabels := match w.parser with
      | .start => []
      | .blocks (_ + 1) => w.bodyLabels ++ [L]
      | _ => w.bodyLabels
    leafIndex := match w.parser with
      | .leaves _ _ => w.leafIndex + 1
      | _ => 0
    rootMarker := match w.parser with
      | .start => n
      | _ => w.rootMarker
    bodyMarker := match w.parser with
      | .start => 0
      | .blocks (_ + 1) => n
      | _ => w.bodyMarker }

def read (w : LabeledWord) (L : Finset ℕ) (n : ℕ) : Option LabeledWord :=
  (Parser.step w.parser n).map (w.record L n)

/-- Nonempty labels are allowed at the root and at selected body
markers only. Label values must be positive and strictly below their
marker. Freshness of the values is a separate global condition. -/
def AllowedLabel (w : LabeledWord) (L : Finset ℕ) (n : ℕ) : Prop :=
  (∀ i ∈ L, 0 < i ∧ i < n) ∧
  match w.parser with
  | .start => True
  | .blocks 0 => False
  | .blocks (_ + 1) => w.bodyLabels.length + 1 ∉ w.rootLabel → L = ∅
  | .leaves _ _ => L = ∅

theorem read_spec {w w' : LabeledWord} {L : Finset ℕ} {n : ℕ}
    (h : w.read L n = some w') :
    Parser.step w.parser n = some w'.parser ∧
      w'.coordinates = w.coordinates ++ [n] := by
  cases hs : Parser.step w.parser n with
  | none => simp [read, hs] at h
  | some s =>
      have heq : w.record L n s = w' := by simpa [read, hs] using h
      subst w'
      exact ⟨rfl, rfl⟩

theorem read_exists {w : LabeledWord} (hw : w.terminal = false)
    (L : Finset ℕ) (n : ℕ) : ∃ w', w.read L n = some w' := by
  have hne : w.parser ≠ .blocks 0 := by simpa [terminal] using hw
  obtain ⟨s, hs⟩ := Parser.step_exists hne n
  exact ⟨w.record L n s, by simp [read, hs]⟩

theorem read_decreases {w w' : LabeledWord} {L : Finset ℕ} {n : ℕ}
    (h : w.read L n = some w') : Parser.potential w'.parser < Parser.potential w.parser :=
  Parser.step_decreases (read_spec h).1

theorem read_nonterminal {w w' : LabeledWord} {L : Finset ℕ} {n : ℕ}
    (h : w.read L n = some w') : w.terminal = false := by
  have hstep := (read_spec h).1
  have hne : w.parser ≠ .blocks 0 := by
    intro hs
    simp [hs, Parser.step] at hstep
  simpa [terminal] using hne

theorem read_wellFounded :
    WellFounded (fun w' w : LabeledWord => ∃ L n, w.read L n = some w') :=
  (InvImage.wf (fun w : LabeledWord => Parser.potential w.parser) wellFounded_lt).mono
    fun _ _ h => read_decreases h.choose_spec.choose_spec

def Parsed (w : LabeledWord) : Prop :=
  Parser.run .start w.coordinates = some w.parser

@[simp] theorem parsed_initial : initial.Parsed := rfl

theorem Parsed.read {w w' : LabeledWord} (hw : w.Parsed)
    {L : Finset ℕ} {n : ℕ} (h : w.read L n = some w') : w'.Parsed := by
  obtain ⟨hstep, hcoords⟩ := read_spec h
  change Parser.run .start w'.coordinates = some w'.parser
  rw [hcoords, Parser.run_append, hw]
  simp [Parser.run, hstep]

theorem allowed_empty {w : LabeledWord} (hw : w.terminal = false) (n : ℕ) :
    w.AllowedLabel ∅ n := by
  have hne : w.parser ≠ .blocks 0 := by simpa [terminal] using hw
  refine ⟨by simp, ?_⟩
  cases hs : w.parser with
  | start => trivial
  | leaves r b => rfl
  | blocks r =>
      cases r with
      | zero => exact (hne hs).elim
      | succ r => exact fun _ => rfl

def AllowedSize (w : LabeledWord) (d : ℕ) : Prop :=
  w.terminal = false ∧ (d = 0 ∨ w.parser = .start ∨ w.markerEvent = true)

theorem allowedLabel_of_size {w : LabeledWord} {d n : ℕ} {L : Finset ℕ}
    (hd : w.AllowedSize d) (hcard : L.card = d)
    (hbound : ∀ i ∈ L, 0 < i ∧ i < n) : w.AllowedLabel L n := by
  have hempty (hz : d = 0) : L = ∅ := Finset.card_eq_zero.mp (hcard.trans hz)
  refine ⟨hbound, ?_⟩
  cases hs : w.parser with
  | start => trivial
  | blocks r =>
      cases r with
      | zero => simp [AllowedSize, terminal, hs] at hd
      | succ r =>
          intro hi
          rcases hd.2 with hz | hstart | hm
          · exact hempty hz
          · simp [hs] at hstart
          · simp [markerEvent, hs, hi] at hm
  | leaves r b =>
      rcases hd.2 with hz | hstart | hm
      · exact hempty hz
      · simp [hs] at hstart
      · simp [markerEvent, hs] at hm

theorem event_false_terminal {w : LabeledWord} (h : w.event = false) :
    w.terminal = false := by
  have hs : (w.terminal = false ∧ w.relaxed = false) ∧ w.markerEvent = false := by
    simpa only [event, Bool.or_eq_false_iff] using h
  exact hs.1.1

/-- The remainder of an advance response, after its first new word
coordinate and attached label have been read. It stops before a later
selected-body marker, at a selected leaf, or at completion. -/
def advanceRemainder : ResponseParser LabeledWord where
  stopped := event
  step w n := w.read ∅ n
  wellFounded := read_wellFounded.mono fun _ _ h => ⟨∅, h⟩
  live_step _w hw n := read_exists (event_false_terminal hw) ∅ n

/-- A finish response gives the empty label to every newly encountered
marker, preserving labels already stored in the cursor. -/
def finishParser : ResponseParser LabeledWord where
  stopped := terminal
  step w n := w.read ∅ n
  wellFounded := read_wellFounded.mono fun _ _ h => ⟨∅, h⟩
  live_step _w hw n := read_exists hw ∅ n

theorem advanceRemainder_thin (w : LabeledWord) :
    Erdos590.Larson.NashWilliams.FinThin (advanceRemainder.family w) :=
  advanceRemainder.family_thin w

theorem advanceRemainder_exists (w : LabeledWord) {H : Set ℕ} (hH : H.Infinite) :
    ∃ u, u ∈ advanceRemainder.family w ∧ (↑u : Set ℕ) ⊆ H :=
  advanceRemainder.family_exists w hH

theorem finish_thin (w : LabeledWord) :
    Erdos590.Larson.NashWilliams.FinThin (finishParser.family w) :=
  finishParser.family_thin w

theorem finish_exists (w : LabeledWord) {H : Set ℕ} (hH : H.Infinite) :
    ∃ u, u ∈ finishParser.family w ∧ (↑u : Set ℕ) ⊆ H :=
  finishParser.family_exists w hH

theorem advanceRemainder_spec {w w' : LabeledWord} {xs : List ℕ}
    (hw : w.Parsed) (h : advanceRemainder.run w xs = some w') :
    w'.Parsed ∧ w'.coordinates = w.coordinates ++ xs ∧ w'.event = true := by
  refine ⟨?_, ?_, advanceRemainder.run_stopped h⟩
  · exact advanceRemainder.run_invariant Parsed
      (fun _ _ _ hp hread => hp.read hread) hw h
  · exact advanceRemainder.run_accumulator coordinates
      (fun _ _ _ hread => (read_spec hread).2) h

theorem finish_spec {w w' : LabeledWord} {xs : List ℕ}
    (hw : w.Parsed) (h : finishParser.run w xs = some w') :
    w'.Parsed ∧ w'.coordinates = w.coordinates ++ xs ∧ w'.terminal = true := by
  refine ⟨?_, ?_, finishParser.run_stopped h⟩
  · exact finishParser.run_invariant Parsed
      (fun _ _ _ hp hread => hp.read hread) hw h
  · exact finishParser.run_accumulator coordinates
      (fun _ _ _ hread => (read_spec hread).2) h

theorem terminal_good {w : LabeledWord} (hw : w.Parsed)
    (hinc : w.coordinates.Pairwise (· < ·)) (hterm : w.terminal = true) :
    ∃ g : Erdos591.Negative.Exact.G, Erdos591.Negative.Exact.word g.val = w.coordinates := by
  apply (Parser.run_start_iff_good w.coordinates hinc).1
  have hs : w.parser = .blocks 0 := by simpa [terminal] using hterm
  simpa only [Parsed, hs] using hw

/-- Finishing a parsed increasing prefix with increasing fresh inputs
produces a vertex of the exact carrier, not just an abstract nested list. -/
theorem finish_good {w w' : LabeledWord} {xs : List ℕ}
    (hw : w.Parsed) (hinc : w.coordinates.Pairwise (· < ·))
    (hxs : xs.Pairwise (· < ·)) (hsep : ∀ x ∈ w.coordinates, ∀ y ∈ xs, x < y)
    (h : finishParser.run w xs = some w') :
    ∃ g : Erdos591.Negative.Exact.G, Erdos591.Negative.Exact.word g.val = w'.coordinates := by
  obtain ⟨hp, hcoords, hterm⟩ := finish_spec hw h
  apply terminal_good hp _ hterm
  rw [hcoords]
  exact List.pairwise_append.mpr ⟨hinc, hxs, hsep⟩

def outstandingBodies : Parser.State → ℕ
  | .start => 0
  | .blocks r => r
  | .leaves r _ => r

def outstandingLeaves : Parser.State → ℕ
  | .leaves _ b => b + 1
  | _ => 0

@[simp] theorem outstandingBodies_normalize (r b : ℕ) :
    outstandingBodies (Parser.normalize r b) = r := by
  cases b <;> rfl

@[simp] theorem outstandingLeaves_normalize (r b : ℕ) :
    outstandingLeaves (Parser.normalize r b) = b := by
  cases b <;> rfl

def Counters (w : LabeledWord) : Prop :=
  w.bodyLabels.length + outstandingBodies w.parser = w.rootMarker ∧
    w.leafIndex + outstandingLeaves w.parser = w.bodyMarker

def CurrentBounds (w : LabeledWord) : Prop :=
  (∀ i ∈ w.rootLabel, 0 < i ∧ i < w.rootMarker) ∧
    (∀ j ∈ w.currentLabel, 0 < j ∧ j < w.bodyMarker)

@[simp] theorem counters_initial : initial.Counters := by
  simp [Counters, initial, outstandingBodies, outstandingLeaves]

@[simp] theorem currentBounds_initial : initial.CurrentBounds := by
  simp [CurrentBounds, initial, currentLabel]

theorem Counters.read {w w' : LabeledWord} (hw : w.Counters)
    {L : Finset ℕ} {n : ℕ} (h : w.read L n = some w') : w'.Counters := by
  cases hs : w.parser with
  | start =>
      have heq : w.record L n (.blocks n) = w' := by
        simpa [LabeledWord.read, hs, Parser.step] using h
      subst w'
      simp [Counters, record, hs, outstandingBodies, outstandingLeaves]
  | blocks r =>
      cases r with
      | zero => simp [LabeledWord.read, hs, Parser.step] at h
      | succ r =>
          have heq : w.record L n (Parser.normalize r n) = w' := by
            simpa [LabeledWord.read, hs, Parser.step] using h
          subst w'
          simp only [Counters, hs, outstandingBodies, outstandingLeaves, Nat.add_zero] at hw
          obtain ⟨hbody, hleaf⟩ := hw
          simp only [Counters, record, hs, List.length_append, List.length_singleton,
            outstandingBodies_normalize, outstandingLeaves_normalize, Nat.zero_add]
          exact ⟨by omega, trivial⟩
  | leaves r b =>
      have heq : w.record L n (Parser.normalize r b) = w' := by
        simpa [LabeledWord.read, hs, Parser.step] using h
      subst w'
      simp only [Counters, hs, outstandingBodies, outstandingLeaves] at hw
      obtain ⟨hbody, hleaf⟩ := hw
      simp only [Counters, record, hs, outstandingBodies_normalize, outstandingLeaves_normalize]
      constructor <;> omega

theorem CurrentBounds.read {w w' : LabeledWord} (hw : w.CurrentBounds)
    {L : Finset ℕ} {n : ℕ} (hL : w.AllowedLabel L n)
    (h : w.read L n = some w') : w'.CurrentBounds := by
  cases hs : w.parser with
  | start =>
      have heq : w.record L n (.blocks n) = w' := by
        simpa [LabeledWord.read, hs, Parser.step] using h
      subst w'
      simpa [CurrentBounds, record, hs, currentLabel] using hL.1
  | blocks r =>
      cases r with
      | zero => simp [LabeledWord.read, hs, Parser.step] at h
      | succ r =>
          have heq : w.record L n (Parser.normalize r n) = w' := by
            simpa [LabeledWord.read, hs, Parser.step] using h
          subst w'
          simpa [CurrentBounds, record, hs, currentLabel, List.getLastD_concat] using
            (show (∀ i ∈ w.rootLabel, 0 < i ∧ i < w.rootMarker) ∧
              (∀ j ∈ L, 0 < j ∧ j < n) from ⟨hw.1, hL.1⟩)
  | leaves r b =>
      have heq : w.record L n (Parser.normalize r b) = w' := by
        simpa [LabeledWord.read, hs, Parser.step] using h
      subst w'
      simpa [CurrentBounds, record, hs, currentLabel] using hw

/-- A selected leaf is strictly before the last leaf of its body and
strictly before the last body. These facts follow from the literal
marker counts and strict label bounds. -/
theorem relaxed_outstanding {w : LabeledWord} (hc : w.Counters)
    (hb : w.CurrentBounds) (hr : w.relaxed = true) :
    0 < outstandingBodies w.parser ∧ 0 < outstandingLeaves w.parser := by
  have hrel : 0 < w.leafIndex ∧ w.bodyLabels.length ∈ w.rootLabel ∧
      w.leafIndex ∈ w.currentLabel := by simpa [relaxed] using hr
  have hi := (hb.1 _ hrel.2.1).2
  have hj := (hb.2 _ hrel.2.2).2
  obtain ⟨hbody, hleaf⟩ := hc
  constructor <;> omega

theorem relaxed_not_terminal {w : LabeledWord} (hc : w.Counters)
    (hb : w.CurrentBounds) (hr : w.relaxed = true) : w.terminal = false := by
  have hout := (relaxed_outstanding hc hb hr).2
  cases hs : w.parser with
  | start => simp [hs, outstandingLeaves] at hout
  | blocks r => simp [hs, outstandingLeaves] at hout
  | leaves r b => simp [terminal, hs]

theorem relaxed_not_marker {w : LabeledWord} (hc : w.Counters)
    (hb : w.CurrentBounds) (hr : w.relaxed = true) : w.markerEvent = false := by
  have hout := (relaxed_outstanding hc hb hr).2
  cases hs : w.parser with
  | start => simp [hs, outstandingLeaves] at hout
  | blocks r => simp [hs, outstandingLeaves] at hout
  | leaves r b => simp [markerEvent, hs]

theorem finish_potential_le {w w' : LabeledWord} {xs : List ℕ}
    (h : finishParser.run w xs = some w') :
    Parser.potential w'.parser ≤ Parser.potential w.parser := by
  apply finishParser.run_invariant
    (fun u => Parser.potential u.parser ≤ Parser.potential w.parser) ?_ (le_refl _) h
  intro u n v hu huv
  exact (read_decreases huv).le.trans hu

theorem finish_decreases {w w' : LabeledWord} {xs : List ℕ}
    (hw : w.terminal = false) (h : finishParser.run w xs = some w') :
    Parser.potential w'.parser < Parser.potential w.parser := by
  cases xs with
  | nil => simp [ResponseParser.run, finishParser, hw] at h
  | cons n xs =>
      obtain ⟨u, hu⟩ := read_exists hw ∅ n
      have ht : finishParser.run u xs = some w' := by
        simpa [ResponseParser.run, finishParser, hw, hu] using h
      exact (finish_potential_le ht).trans_lt (read_decreases hu)

/-- Local bookkeeping needed by the concrete game histories. This does
not include global freshness or the final pair's clarity predicate. -/
def CursorInvariant (w : LabeledWord) : Prop := w.Parsed ∧ w.Counters ∧ w.CurrentBounds

@[simp] theorem cursorInvariant_initial : initial.CursorInvariant :=
  ⟨parsed_initial, counters_initial, currentBounds_initial⟩

theorem CursorInvariant.read {w w' : LabeledWord} (hw : w.CursorInvariant)
    {L : Finset ℕ} {n : ℕ} (hL : w.AllowedLabel L n) (h : w.read L n = some w') :
    w'.CursorInvariant :=
  ⟨hw.1.read h, hw.2.1.read h, hw.2.2.read hL h⟩

theorem advanceRemainder_invariant {w w' : LabeledWord} {xs : List ℕ}
    (hw : w.CursorInvariant) (h : advanceRemainder.run w xs = some w') :
    w'.CursorInvariant := by
  apply advanceRemainder.run_invariant CursorInvariant ?_ hw h
  intro u n v hu huv
  exact hu.read (allowed_empty (read_nonterminal huv) n) huv

theorem finish_invariant {w w' : LabeledWord} {xs : List ℕ}
    (hw : w.CursorInvariant) (h : finishParser.run w xs = some w') :
    w'.CursorInvariant := by
  apply finishParser.run_invariant CursorInvariant ?_ hw h
  intro u n v hu huv
  exact hu.read (allowed_empty (read_nonterminal huv) n) huv

#print axioms advanceRemainder_exists
#print axioms finish_exists
#print axioms finish_good
#print axioms relaxed_outstanding

end LabeledWord

end Erdos591.Positive.Game

end Erdos118.Reused591
