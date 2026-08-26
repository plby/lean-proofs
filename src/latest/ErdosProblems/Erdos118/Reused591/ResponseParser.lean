import ErdosProblems.Erdos590
import Mathlib.Data.List.OfFn

namespace Erdos118.Reused591

/-!
# First-event response blocks

A deterministic input parser with a well-founded transition relation
stops at its first designated event. Its accepted increasing input
lists form a thin family meeting every infinite input set. This is the
general form of the response-block argument, allowing the state to
contain labels and partial words rather than only body counters.
-/

namespace Erdos591.Positive.Game

structure ResponseParser (Q : Type*) where
  stopped : Q → Bool
  step : Q → ℕ → Option Q
  wellFounded : WellFounded (fun q p => ∃ n, step p n = some q)
  live_step : ∀ q, stopped q = false → ∀ n, ∃ q', step q n = some q'

namespace ResponseParser

variable {Q : Type*} (D : ResponseParser Q)

def run (q : Q) : List ℕ → Option Q
  | [] => if D.stopped q then some q else none
  | n :: ns => if D.stopped q then none else (D.step q n).bind fun q' => run q' ns

theorem run_stopped {q r : Q} {xs : List ℕ} (h : D.run q xs = some r) :
    D.stopped r = true := by
  induction xs generalizing q with
  | nil =>
      cases hs : D.stopped q with
      | false => simp [run, hs] at h
      | true =>
          have hqr : q = r := by simpa [run, hs] using h
          exact hqr ▸ hs
  | cons x xs ih =>
      cases hs : D.stopped q with
      | true => simp [run, hs] at h
      | false =>
          cases ht : D.step q x with
          | none => simp [run, hs, ht] at h
          | some t =>
              apply ih (q := t)
              simpa [run, hs, ht] using h

theorem run_nil_of_stopped {q r : Q} {xs : List ℕ}
    (hq : D.stopped q = true) (h : D.run q xs = some r) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [run, hq] at h

theorem no_extension {q r t : Q} {xs ys : List ℕ}
    (hx : D.run q xs = some r) (hxy : D.run q (xs ++ ys) = some t) : ys = [] := by
  induction xs generalizing q with
  | nil =>
      cases hs : D.stopped q with
      | false => simp [run, hs] at hx
      | true => exact D.run_nil_of_stopped hs hxy
  | cons x xs ih =>
      cases hs : D.stopped q with
      | true => simp [run, hs] at hx
      | false =>
          cases ht : D.step q x with
          | none => simp [run, hs, ht] at hx
          | some u =>
              apply ih (q := u)
              · simpa [run, hs, ht] using hx
              · simpa [run, hs, ht] using hxy

theorem terminates (q : Q) (f : ℕ → ℕ) :
    ∃ n r, D.run q (List.ofFn (fun i : Fin n => f i.val)) = some r := by
  revert f
  apply D.wellFounded.induction q
  intro q ih f
  cases hs : D.stopped q with
  | true => exact ⟨0, q, by simp [run, hs]⟩
  | false =>
      obtain ⟨r, hr⟩ := D.live_step q hs (f 0)
      obtain ⟨n, t, ht⟩ := ih r ⟨f 0, hr⟩ (fun i => f (i + 1))
      refine ⟨n + 1, t, ?_⟩
      simpa [List.ofFn_succ, run, hs, hr] using ht

def family (q : Q) : Set (Finset ℕ) :=
  {u | ∃ r, D.run q (u.sort (· ≤ ·)) = some r}

theorem family_thin (q : Q) : Erdos590.Larson.NashWilliams.FinThin (D.family q) := by
  intro u hu v hv huv
  obtain ⟨r, hr⟩ := hu
  obtain ⟨t, ht⟩ := hv
  have hprefix : u.sort (· ≤ ·) <+: v.sort (· ≤ ·) := by
    apply (Erdos590.Larson.pairwise_isPrefix_iff_initSeg
      (Finset.sortedLT_sort u).pairwise (Finset.sortedLT_sort v).pairwise).2
    simpa using huv
  obtain ⟨ys, hys⟩ := hprefix
  have hrun : D.run q (u.sort (· ≤ ·) ++ ys) = some t := hys ▸ ht
  have hnil := D.no_extension hr hrun
  have heq : u.sort (· ≤ ·) = v.sort (· ≤ ·) := by simpa [hnil] using hys
  simpa using congrArg List.toFinset heq

theorem family_exists (q : Q) {H : Set ℕ} (hH : H.Infinite) :
    ∃ u, u ∈ D.family q ∧ (↑u : Set ℕ) ⊆ H := by
  let f := Erdos590.Larson.enumOf H
  obtain ⟨n, r, hn⟩ := D.terminates q f
  let xs := List.ofFn (fun i : Fin n => f i.val)
  have hinc : xs.Pairwise (· < ·) := List.pairwise_ofFn.mpr fun _ _ hij =>
    Erdos590.Larson.enumOf_strictMono hH hij
  refine ⟨xs.toFinset, ?_, ?_⟩
  · refine ⟨r, ?_⟩
    rw [Erdos590.Larson.sort_toFinset_eq_self_of_pairwise hinc]
    exact hn
  · intro x hx
    have hx' : x ∈ xs := List.mem_toFinset.mp hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx'
    exact Erdos590.Larson.enumOf_mem hH i.val

/-- A live parser cannot return an empty response. -/
theorem family_nonempty {q : Q} (hq : D.stopped q = false)
    {u : Finset ℕ} (hu : u ∈ D.family q) : u.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro heq
  obtain ⟨r, hr⟩ := hu
  simp [heq, run, hq] at hr

theorem run_invariant (R : Q → Prop)
    (hstep : ∀ q n r, R q → D.step q n = some r → R r)
    {q r : Q} {xs : List ℕ} (hq : R q) (h : D.run q xs = some r) : R r := by
  induction xs generalizing q with
  | nil =>
      cases hs : D.stopped q with
      | false => simp [run, hs] at h
      | true =>
          have heq : q = r := by simpa [run, hs] using h
          exact heq ▸ hq
  | cons n xs ih =>
      cases hs : D.stopped q with
      | true => simp [run, hs] at h
      | false =>
          cases ht : D.step q n with
          | none => simp [run, hs, ht] at h
          | some t =>
              apply ih (hstep q n t hq ht)
              simpa [run, hs, ht] using h

theorem run_invariant_on (R : Q → Prop) (S : ℕ → Prop)
    (hstep : ∀ q n r, R q → S n → D.step q n = some r → R r)
    {q r : Q} {xs : List ℕ} (hq : R q) (hS : ∀ n ∈ xs, S n)
    (h : D.run q xs = some r) : R r := by
  induction xs generalizing q with
  | nil =>
      cases hs : D.stopped q with
      | false => simp [run, hs] at h
      | true =>
          have heq : q = r := by simpa [run, hs] using h
          exact heq ▸ hq
  | cons n xs ih =>
      cases hs : D.stopped q with
      | true => simp [run, hs] at h
      | false =>
          cases ht : D.step q n with
          | none => simp [run, hs, ht] at h
          | some t =>
              apply ih (hstep q n t hq (hS n (by simp)) ht)
                (fun m hm => hS m (List.mem_cons_of_mem n hm))
              simpa [run, hs, ht] using h

/-- A parser that records each input records exactly its accepted
response, with no hidden, discarded, or duplicated entries. -/
theorem run_accumulator (content : Q → List ℕ)
    (hstep : ∀ q n r, D.step q n = some r → content r = content q ++ [n])
    {q r : Q} {xs : List ℕ} (h : D.run q xs = some r) :
    content r = content q ++ xs := by
  induction xs generalizing q with
  | nil =>
      cases hs : D.stopped q with
      | false => simp [run, hs] at h
      | true =>
          have heq : q = r := by simpa [run, hs] using h
          simp [heq]
  | cons n xs ih =>
      cases hs : D.stopped q with
      | true => simp [run, hs] at h
      | false =>
          cases ht : D.step q n with
          | none => simp [run, hs, ht] at h
          | some t =>
              have hrun : D.run t xs = some r := by simpa [run, hs, ht] using h
              rw [ih hrun, hstep q n t ht]
              simp only [List.append_assoc, List.singleton_append]

#print axioms family_thin
#print axioms family_exists

end ResponseParser

end Erdos591.Positive.Game

end Erdos118.Reused591
