/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# Bounded replacement processes reach a terminal state

This file isolates the well-foundedness argument used at the end of
Pham--Zakharov Lemma 10.  It is intentionally independent of the arithmetic
meaning of a replacement step: if every nonterminal reachable state admits a
next step, but every trace from the initial state has a common finite length
bound, then a reachable terminal state exists.

The result is useful here because the quantitative part of Lemma 10 supplies
the common length bound, while failure of irreducibility supplies a next
replacement.  No maximality principle or hidden termination assumption is
used.
-/

namespace Erdos186.PZ.Reduction

noncomputable section

/-- A total presentation of a finite prefix of a binary relation.  Only the
states and steps before `length` are relevant. -/
structure RelationTrace {State : Type*} (step : State → State → Prop)
    (initial : State) (length : ℕ) where
  state : ℕ → State
  state_zero : state 0 = initial
  valid : ∀ i, i < length → step (state i) (state (i + 1))

namespace RelationTrace

variable {State : Type*} {step : State → State → Prop}
  {initial : State} {length : ℕ}

/-- Every state occurring in a relation trace is reachable from its initial
state. -/
theorem reachable (T : RelationTrace step initial length) {m : ℕ}
    (hm : m ≤ length) : Relation.ReflTransGen step initial (T.state m) := by
  induction m with
  | zero => simpa [T.state_zero] using
      (Relation.ReflTransGen.refl :
        Relation.ReflTransGen step initial initial)
  | succ m ih =>
      exact (ih (by omega)).tail (T.valid m (by omega))

end RelationTrace

/-- If all traces from `initial` have length at most `bound`, and every
reachable nonterminal state can be extended, some terminal state is reachable
in at most `bound` steps.

This is the precise logical termination principle used in the irreducible
replacement argument. -/
theorem exists_reachable_terminal_of_trace_bound
    {State : Type*} (step : State → State → Prop)
    (terminal : State → Prop) (initial : State) (bound : ℕ)
    (extend : ∀ S, Relation.ReflTransGen step initial S →
      ¬ terminal S → ∃ T, step S T)
    (trace_bound : ∀ {length : ℕ},
      RelationTrace step initial length → length ≤ bound) :
    ∃ S, Relation.ReflTransGen step initial S ∧ terminal S := by
  classical
  by_contra hterminal
  push Not at hterminal
  let Reachable := {S : State // Relation.ReflTransGen step initial S}
  have next_exists (S : Reachable) : ∃ T, step S.1 T :=
    extend S.1 S.2 (hterminal S.1 S.2)
  let next (S : Reachable) : State := Classical.choose (next_exists S)
  have next_step (S : Reachable) : step S.1 (next S) :=
    Classical.choose_spec (next_exists S)
  let advance (S : Reachable) : Reachable :=
    ⟨next S, S.2.tail (next_step S)⟩
  let start : Reachable := ⟨initial, Relation.ReflTransGen.refl⟩
  let states : ℕ → State := fun n ↦ ((advance^[n]) start).1
  have states_zero : states 0 = initial := by
    simp [states, start]
  have states_step (i : ℕ) : step (states i) (states (i + 1)) := by
    simpa [states, Function.iterate_succ_apply', advance] using
      next_step ((advance^[i]) start)
  let T : RelationTrace step initial (bound + 1) :=
    { state := states
      state_zero := states_zero
      valid := fun i _hi ↦ states_step i }
  have := trace_bound T
  omega

end

end Erdos186.PZ.Reduction
