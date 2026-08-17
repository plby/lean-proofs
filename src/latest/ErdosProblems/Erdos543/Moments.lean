/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import Mathlib

/-!
# Falling factorial moments of finite event families

This file records the elementary combinatorial identity behind factorial-moment
arguments.  The `r`th descending factorial of the number of events occurring at
a sample point counts ordered injective `r`-tuples of simultaneously occurring
events.  Summing over a finite sample space gives the corresponding exact
factorial-moment formula.
-/

open scoped BigOperators
open Finset

namespace Erdos543

attribute [local instance] Classical.propDecidable

/-! ## Event counts -/

/-- The number of members of a finite event family which occur at `ω`. -/
noncomputable def eventCount {Ω E : Type*} [Fintype E]
    (event : E → Ω → Prop) (ω : Ω) : ℕ := by
  classical
  exact (Finset.univ.filter fun e ↦ event e ω).card

/-- The number of sample points at which all events selected by an ordered
injective `r`-tuple occur. -/
noncomputable def jointEventCount {Ω E : Type*} [Fintype Ω]
    (event : E → Ω → Prop) {r : ℕ} (ι : Fin r ↪ E) : ℕ := by
  classical
  exact (Finset.univ.filter fun ω ↦ ∀ i, event (ι i) ω).card

/-! ## The pointwise counting identity -/

/-- At a fixed sample point, the descending factorial of the event count is
the number of ordered injective tuples of events which all occur. -/
theorem descFactorial_eventCount {Ω E : Type*} [Fintype E]
    (event : E → Ω → Prop) (ω : Ω) (r : ℕ) :
    (eventCount event ω).descFactorial r =
      (Finset.univ.filter fun ι : Fin r ↪ E ↦ ∀ i, event (ι i) ω).card := by
  classical
  change ((Finset.univ.filter fun e : E ↦ event e ω).card).descFactorial r = _
  calc
    ((Finset.univ.filter fun e : E ↦ event e ω).card).descFactorial r =
        (Fintype.card {e : E // event e ω}).descFactorial r := by
      congr 1
      exact (Fintype.card_subtype (fun e : E ↦ event e ω)).symm
    _ = Fintype.card (Fin r ↪ {e : E // event e ω}) := by
      rw [Fintype.card_embedding_eq, Fintype.card_fin]
    _ = Fintype.card {ι : Fin r ↪ E // ∀ i, event (ι i) ω} := by
      exact Fintype.card_congr (Equiv.codRestrict (Fin r) {e : E | event e ω}).symm
    _ = (Finset.univ.filter fun ι : Fin r ↪ E ↦ ∀ i, event (ι i) ω).card := by
      exact Fintype.card_subtype (fun ι : Fin r ↪ E ↦ ∀ i, event (ι i) ω)

/-- Sum form of `descFactorial_eventCount`: each ordered injective tuple
contributes its indicator. -/
theorem descFactorial_eventCount_eq_sum_indicator {Ω E : Type*} [Fintype E]
    (event : E → Ω → Prop) (ω : Ω) (r : ℕ) :
    (eventCount event ω).descFactorial r =
      ∑ ι : Fin r ↪ E, if ∀ i, event (ι i) ω then 1 else 0 := by
  rw [descFactorial_eventCount]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-! ## Summation over a finite sample space -/

/-- Exact unnormalised falling-factorial moment identity.  The sum of the
`r`th descending factorial of the number of occurring events equals the sum,
over ordered injective `r`-tuples of events, of their joint occurrence counts. -/
theorem sum_descFactorial_eventCount {Ω E : Type*} [Fintype Ω] [Fintype E]
    (event : E → Ω → Prop) (r : ℕ) :
    (∑ ω : Ω, (eventCount event ω).descFactorial r) =
      ∑ ι : Fin r ↪ E, jointEventCount event ι := by
  classical
  simp_rw [descFactorial_eventCount_eq_sum_indicator]
  unfold jointEventCount
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- The exact factorial-moment identity after casting into any characteristic
zero semiring. -/
theorem sum_descFactorial_eventCount_cast {Ω E R : Type*}
    [Fintype Ω] [Fintype E] [Semiring R] [CharZero R]
    (event : E → Ω → Prop) (r : ℕ) :
    (∑ ω : Ω, ((eventCount event ω).descFactorial r : R)) =
      ∑ ι : Fin r ↪ E, (jointEventCount event ι : R) := by
  exact_mod_cast sum_descFactorial_eventCount event r

/-- Uniformly normalised version of the factorial-moment identity.  No
nonemptiness assumption is needed: both sides use the same denominator. -/
theorem uniformAverage_descFactorial_eventCount {Ω E R : Type*}
    [Fintype Ω] [Fintype E] [DivisionSemiring R] [CharZero R]
    (event : E → Ω → Prop) (r : ℕ) :
    (∑ ω : Ω, ((eventCount event ω).descFactorial r : R)) /
        (Fintype.card Ω : R) =
      (∑ ι : Fin r ↪ E, (jointEventCount event ι : R)) /
        (Fintype.card Ω : R) := by
  rw [sum_descFactorial_eventCount_cast]

end Erdos543
