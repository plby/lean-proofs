import ErdosProblems.Erdos118.Reused591.ExactGoodSequence
import Mathlib.Data.List.OfFn
import Mathlib.Data.Prod.Lex
import Mathlib.Order.WithBot

namespace Erdos118.Reused591

/-!
# The self-delimiting height-two word parser

The accepted words are exactly the literal words used for the checked
negative relation. The parser's well-founded potential is represented
by `WithTop (ℕ ×ₗ ℕ)`: the top element is the initial state, and `(r,b)`
represents the ordinal `omega * r + b`. There is no fuel parameter or
assumed termination bound.
-/

namespace Erdos591.Positive.Game.Parser

open Erdos591.Negative.Exact

inductive State where
  | start
  | blocks (remaining : ℕ)
  /-- There are `b + 1` leaves left in this body, and `r` later bodies. -/
  | leaves (r b : ℕ)
  deriving DecidableEq

def normalize (r : ℕ) : ℕ → State
  | 0 => .blocks r
  | b + 1 => .leaves r b

def step : State → ℕ → Option State
  | .start, n => some (.blocks n)
  | .blocks 0, _ => none
  | .blocks (r + 1), n => some (normalize r n)
  | .leaves r b, _ => some (normalize r b)

def potential : State → WithTop (ℕ ×ₗ ℕ)
  | .start => ⊤
  | .blocks r => ↑(toLex (r, 0))
  | .leaves r b => ↑(toLex (r, b + 1))

@[simp] theorem potential_normalize (r b : ℕ) :
    potential (normalize r b) = ↑(toLex (r, b)) := by
  cases b <;> rfl

theorem step_decreases {s t : State} {n : ℕ} (h : step s n = some t) :
    potential t < potential s := by
  cases s with
  | start =>
      simp only [step, Option.some.injEq] at h
      subst t
      exact WithTop.coe_lt_top _
  | blocks r =>
      cases r with
      | zero => simp [step] at h
      | succ r =>
          simp only [step, Option.some.injEq] at h
          subst t
          rw [potential_normalize]
          apply WithTop.coe_lt_coe.mpr
          exact Prod.Lex.left _ _ (Nat.lt_succ_self r)
  | leaves r b =>
      simp only [step, Option.some.injEq] at h
      subst t
      rw [potential_normalize]
      apply WithTop.coe_lt_coe.mpr
      exact Prod.Lex.right _ (Nat.lt_succ_self b)

theorem step_wellFounded : WellFounded (fun t s => ∃ n, step s n = some t) :=
  (InvImage.wf potential wellFounded_lt).mono fun _ _ h =>
    step_decreases h.choose_spec

theorem step_exists {s : State} (hs : s ≠ .blocks 0) (n : ℕ) :
    ∃ t, step s n = some t := by
  cases s with
  | start => exact ⟨.blocks n, rfl⟩
  | blocks r =>
      cases r with
      | zero => exact (hs rfl).elim
      | succ r => exact ⟨normalize r n, rfl⟩
  | leaves r b => exact ⟨normalize r b, rfl⟩

def run (s : State) : List ℕ → Option State
  | [] => some s
  | n :: ns => (step s n).bind fun t => run t ns

@[simp] theorem run_nil (s : State) : run s [] = some s := rfl

theorem run_append (s : State) (xs ys : List ℕ) :
    run s (xs ++ ys) = (run s xs).bind (fun t => run t ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
      cases h : step s x with
      | none => simp [run, h]
      | some t => simpa [run, h] using ih t

theorem run_terminal {xs : List ℕ} {t : State}
    (h : run (.blocks 0) xs = some t) : xs = [] ∧ t = .blocks 0 := by
  cases xs with
  | nil => simpa [run] using h.symm
  | cons x xs => simp [run, step] at h

/-- Once a word has terminated, no proper extension can be accepted. -/
theorem no_extension {s t : State} {xs ys : List ℕ}
    (hx : run s xs = some (.blocks 0)) (hxy : run s (xs ++ ys) = some t) :
    ys = [] := by
  rw [run_append, hx] at hxy
  exact (run_terminal hxy).1

theorem run_leaves (r : ℕ) (a : List ℕ) :
    run (normalize r a.length) a = some (.blocks r) := by
  induction a with
  | nil => rfl
  | cons x a ih => simpa [run, normalize, step] using ih

theorem run_levelWord (r : ℕ) (a : List ℕ) :
    run (.blocks (r + 1)) (levelWord a) = some (.blocks r) := by
  simpa [levelWord, run, step] using run_leaves r a

theorem run_bodies (s : List (List ℕ)) :
    run (.blocks s.length) (s.flatMap levelWord) = some (.blocks 0) := by
  induction s with
  | nil => rfl
  | cons a s ih =>
      simp only [List.length_cons, List.flatMap_cons, run_append, run_levelWord,
        Option.bind_some]
      exact ih

@[simp] theorem run_word (s : List (List ℕ)) :
    run .start (word s) = some (.blocks 0) := by
  simpa [word, run, step] using run_bodies s

/-- A successful run through a current body's leaves consumes exactly
the prescribed number of entries before parsing the remaining bodies. -/
theorem split_leaves (r b : ℕ) (xs : List ℕ)
    (h : run (normalize r b) xs = some (.blocks 0)) :
    ∃ a ys, xs = a ++ ys ∧ a.length = b ∧ run (.blocks r) ys = some (.blocks 0) := by
  induction b generalizing xs with
  | zero => exact ⟨[], xs, rfl, rfl, h⟩
  | succ b ih =>
      cases xs with
      | nil => simp [run, normalize] at h
      | cons x xs =>
          have ht : run (normalize r b) xs = some (.blocks 0) := by
            simpa [normalize, run, step] using h
          obtain ⟨a, ys, heq, hlen, hy⟩ := ih xs ht
          refine ⟨x :: a, ys, ?_, ?_, hy⟩
          · simp [heq]
          · simp [hlen]

theorem split_bodies (r : ℕ) (xs : List ℕ)
    (h : run (.blocks r) xs = some (.blocks 0)) :
    ∃ s : List (List ℕ), s.length = r ∧ s.flatMap levelWord = xs := by
  induction r generalizing xs with
  | zero =>
      have hx := (run_terminal h).1
      exact ⟨[], rfl, hx.symm⟩
  | succ r ih =>
      cases xs with
      | nil => simp [run] at h
      | cons b xs =>
          have ht : run (normalize r b) xs = some (.blocks 0) := by
            simpa [run, step] using h
          obtain ⟨a, ys, heq, hlen, hy⟩ := split_leaves r b xs ht
          obtain ⟨s, hslen, hsflat⟩ := ih ys hy
          refine ⟨a :: s, by simp [hslen], ?_⟩
          simp [List.flatMap_cons, levelWord, hsflat, hlen, heq]

/-- The accepting language is exactly the literal height-two words,
before imposing the strictly increasing coordinate condition. -/
theorem run_start_iff (xs : List ℕ) :
    run .start xs = some (.blocks 0) ↔ ∃ s : List (List ℕ), word s = xs := by
  constructor
  · intro h
    cases xs with
    | nil => simp [run] at h
    | cons r xs =>
        have hr : run (.blocks r) xs = some (.blocks 0) := by
          simpa [run, step] using h
        obtain ⟨s, hslen, hsflat⟩ := split_bodies r xs hr
        exact ⟨s, by simp [word, hslen, hsflat]⟩
  · rintro ⟨s, rfl⟩
    exact run_word s

theorem run_start_iff_good (xs : List ℕ) (hxs : xs.Pairwise (· < ·)) :
    run .start xs = some (.blocks 0) ↔ ∃ s : G, word s.val = xs := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (run_start_iff xs).1 h
    exact ⟨⟨s, hs.symm ▸ hxs⟩, hs⟩
  · rintro ⟨s, rfl⟩
    exact run_word s.val

theorem flatMap_levelWord_injective :
    Function.Injective (fun s : List (List ℕ) => s.flatMap levelWord) := by
  intro s t h
  induction s generalizing t with
  | nil =>
      cases t with
      | nil => rfl
      | cons b t => simp [List.flatMap_cons, levelWord] at h
  | cons a s ih =>
      cases t with
      | nil => simp [List.flatMap_cons, levelWord] at h
      | cons b t =>
          have hp : a.length = b.length ∧
              a ++ s.flatMap levelWord = b ++ t.flatMap levelWord := by
            simpa [List.flatMap_cons, levelWord] using h
          have hab := List.append_inj_left hp.2 hp.1
          have hst := ih (List.append_inj_right hp.2 hp.1)
          simp [hab, hst]

/-- Decoding a literal word does not involve a choice of vertex. -/
theorem word_injective : Function.Injective (word : List (List ℕ) → List ℕ) := by
  intro s t h
  apply flatMap_levelWord_injective
  exact (List.cons.inj h).2

/-- Every infinite input stream has a finite accepting initial segment
from every parser state. This follows by well-founded induction, not by
a computational search with an increased limit. -/
theorem terminates (s : State) (f : ℕ → ℕ) :
    ∃ n, run s (List.ofFn (fun i : Fin n => f i.val)) = some (.blocks 0) := by
  revert f
  apply step_wellFounded.induction s
  intro s ih f
  by_cases hs : s = .blocks 0
  · exact ⟨0, by simp [hs]⟩
  · obtain ⟨t, ht⟩ := step_exists hs (f 0)
    obtain ⟨n, hn⟩ := ih t ⟨f 0, ht⟩ (fun i => f (i + 1))
    refine ⟨n + 1, ?_⟩
    simpa [List.ofFn_succ, run, ht] using hn

def completions (s : State) : Set (Finset ℕ) :=
  {u | run s (u.sort (· ≤ ·)) = some (.blocks 0)}

theorem completions_thin (s : State) :
    Erdos590.Larson.NashWilliams.FinThin (completions s) := by
  intro u hu v hv huv
  have hprefix : u.sort (· ≤ ·) <+: v.sort (· ≤ ·) := by
    apply (Erdos590.Larson.pairwise_isPrefix_iff_initSeg
      (Finset.sortedLT_sort u).pairwise (Finset.sortedLT_sort v).pairwise).2
    simpa using huv
  obtain ⟨ys, hys⟩ := hprefix
  have hrun : run s (u.sort (· ≤ ·) ++ ys) = some (.blocks 0) := hys ▸ hv
  have hnil := no_extension hu hrun
  have heq : u.sort (· ≤ ·) = v.sort (· ≤ ·) := by simpa [hnil] using hys
  simpa using congrArg List.toFinset heq

/-- Every infinite set of fresh inputs contains a finite completion.
The increasing input order is inherited from its natural enumeration. -/
theorem completion_exists (s : State) {H : Set ℕ} (hH : H.Infinite) :
    ∃ u, u ∈ completions s ∧ (↑u : Set ℕ) ⊆ H := by
  let f := Erdos590.Larson.enumOf H
  obtain ⟨n, hn⟩ := terminates s f
  let xs := List.ofFn (fun i : Fin n => f i.val)
  have hinc : xs.Pairwise (· < ·) := List.pairwise_ofFn.mpr fun _ _ hij =>
    Erdos590.Larson.enumOf_strictMono hH hij
  refine ⟨xs.toFinset, ?_, ?_⟩
  · change run s (xs.toFinset.sort (· ≤ ·)) = some (.blocks 0)
    rw [Erdos590.Larson.sort_toFinset_eq_self_of_pairwise hinc]
    exact hn
  · intro x hx
    have hx' : x ∈ xs := List.mem_toFinset.mp hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx'
    exact Erdos590.Larson.enumOf_mem hH i.val

theorem run_potential_le {s t : State} {xs : List ℕ}
    (h : run s xs = some t) : potential t ≤ potential s := by
  induction xs generalizing s with
  | nil =>
      have heq : s = t := Option.some.inj h
      exact heq ▸ le_refl _
  | cons x xs ih =>
      cases hstep : step s x with
      | none => simp [run, hstep] at h
      | some u =>
          have hrest : run u xs = some t := by simpa [run, hstep] using h
          exact (ih hrest).trans (step_decreases hstep).le

theorem run_potential_lt {s t : State} {xs : List ℕ}
    (hxs : xs ≠ []) (h : run s xs = some t) : potential t < potential s := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons x xs =>
      cases hstep : step s x with
      | none => simp [run, hstep] at h
      | some u =>
          have hrest : run u xs = some t := by simpa [run, hstep] using h
          exact (run_potential_le hrest).trans_lt (step_decreases hstep)

/-- All parseable finite prefixes, including complete words. -/
def Prefix : Type := {xs : List ℕ // ∃ s, run .start xs = some s}

namespace Prefix

noncomputable def state (p : Prefix) : State := p.property.choose

theorem parses (p : Prefix) : run .start p.val = some p.state :=
  p.property.choose_spec

def ProperExtension (q p : Prefix) : Prop :=
  ∃ ys : List ℕ, ys ≠ [] ∧ p.val ++ ys = q.val

theorem properExtension_decreases {p q : Prefix} (h : ProperExtension q p) :
    potential q.state < potential p.state := by
  obtain ⟨ys, hys, heq⟩ := h
  have hrun := q.parses
  rw [← heq, run_append, p.parses] at hrun
  exact run_potential_lt hys hrun

theorem properExtension_wellFounded : WellFounded ProperExtension :=
  (InvImage.wf (fun p : Prefix => potential p.state) wellFounded_lt).mono
    fun _ _ h => properExtension_decreases h

end Prefix

#print axioms run_start_iff_good
#print axioms completion_exists
#print axioms Prefix.properExtension_wellFounded

end Erdos591.Positive.Game.Parser

end Erdos118.Reused591
