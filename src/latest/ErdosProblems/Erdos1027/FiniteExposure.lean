/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import Mathlib

/-!
# Exposing the coordinates on a finite edge

This file records the elementary finite product-space decomposition used by
the fixed-edge part of the Duraj--Gutowski--Kozik argument.  A function on a
finite vertex type is uniquely determined by its restriction to a finset
`edge` and its restriction to the complement of `edge`.  Consequently, a
sum, a cardinality, or a uniform expectation over all global functions can
be evaluated by first exposing the outside restriction and then summing over
the inside restriction.

The results are deliberately independent of the particular random variables
used in Erdős Problem 1027.  In particular, `card_event_eq_sum_fiber` and
`expect_event_indicator_eq_expect_fiber` can be used for any event on a finite
function space.
-/

namespace Erdos1027.FiniteExposure

open scoped BigOperators
open Finset

/-- Assignments on the coordinates belonging to `edge`. -/
abbrev InsideAssignment {V A : Type*} (edge : Finset V) := (v : ↥edge) → A

/-- Assignments on the coordinates outside `edge`. -/
abbrev OutsideAssignment {V A : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V) :=
  (v : ↥((Finset.univ : Finset V) \ edge)) → A

/-- Glue an outside assignment and an inside assignment into a global one. -/
def glue {V A : Type*} [Fintype V] [DecidableEq V] (edge : Finset V)
    (outside : OutsideAssignment (A := A) edge)
    (inside : InsideAssignment (A := A) edge) : V → A :=
  fun v ↦ if hv : v ∈ edge then inside ⟨v, hv⟩ else outside ⟨v, by simp [hv]⟩

@[simp] lemma glue_apply_of_mem {V A : Type*} [Fintype V] [DecidableEq V]
    {edge : Finset V} (outside : OutsideAssignment (A := A) edge)
    (inside : InsideAssignment (A := A) edge) {v : V} (hv : v ∈ edge) :
    glue edge outside inside v = inside ⟨v, hv⟩ := by
  simp [glue, hv]

@[simp] lemma glue_apply_of_not_mem {V A : Type*} [Fintype V] [DecidableEq V]
    {edge : Finset V} (outside : OutsideAssignment (A := A) edge)
    (inside : InsideAssignment (A := A) edge) {v : V} (hv : v ∉ edge) :
    glue edge outside inside v = outside ⟨v, by simp [hv]⟩ := by
  simp [glue, hv]

/-- The restriction/gluing equivalence, ordered with the exposed outside
coordinates first. -/
def exposureEquiv {V A : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V) :
    (V → A) ≃ OutsideAssignment (A := A) edge × InsideAssignment (A := A) edge where
  toFun f := ⟨fun v ↦ f v, fun v ↦ f v⟩
  invFun p := glue edge p.1 p.2
  left_inv f := by
    funext v
    by_cases hv : v ∈ edge <;> simp [glue, hv]
  right_inv p := by
    apply Prod.ext
    · funext v
      have hv : (v : V) ∉ edge := by
        exact (Finset.mem_sdiff.mp v.2).2
      simp [glue, hv]
    · funext v
      simp [glue, v.2]

@[simp] lemma exposureEquiv_apply {V A : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V) (f : V → A) :
    exposureEquiv edge f = (⟨fun v ↦ f v, fun v ↦ f v⟩ :
      OutsideAssignment (A := A) edge × InsideAssignment (A := A) edge) :=
  rfl

@[simp] lemma exposureEquiv_symm_apply {V A : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V)
    (p : OutsideAssignment (A := A) edge × InsideAssignment (A := A) edge) :
    (exposureEquiv edge).symm p = glue edge p.1 p.2 :=
  rfl

/-- Gluing the two restrictions of a global assignment recovers that
assignment. -/
@[simp] lemma glue_restrictions {V A : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V) (f : V → A) :
    glue edge (fun v : ↥((Finset.univ : Finset V) \ edge) ↦ f v)
      (fun v : ↥edge ↦ f v) = f := by
  funext v
  by_cases hv : v ∈ edge <;> simp [glue, hv]

/-- Decompose a finite sum over global assignments into the exposed outside
assignment and the remaining inside assignment. -/
lemma sum_univ_eq_sum_outside_inside {V A M : Type*}
    [Fintype V] [DecidableEq V] [Fintype A] [AddCommMonoid M]
    (edge : Finset V) (weight : (V → A) → M) :
    (∑ f : V → A, weight f) =
      ∑ outside : OutsideAssignment (A := A) edge,
        ∑ inside : InsideAssignment (A := A) edge,
          weight (glue edge outside inside) := by
  calc
    (∑ f : V → A, weight f) =
        ∑ p : OutsideAssignment (A := A) edge × InsideAssignment (A := A) edge,
          weight ((exposureEquiv edge).symm p) := by
      exact Fintype.sum_equiv (exposureEquiv edge) weight
        (fun p ↦ weight ((exposureEquiv edge).symm p))
        (fun f ↦ by simp)
    _ = ∑ outside : OutsideAssignment (A := A) edge,
          ∑ inside : InsideAssignment (A := A) edge,
            weight (glue edge outside inside) := by
      simpa using (Fintype.sum_prod_type
        (fun p : OutsideAssignment (A := A) edge × InsideAssignment (A := A) edge ↦
          weight ((exposureEquiv edge).symm p)))

/-- A bound proved separately on every exposed fiber can be summed without
any loss over the whole product space. -/
lemma sum_univ_le_sum_outside_of_fiber_bound {V A M : Type*}
    [Fintype V] [DecidableEq V] [Fintype A]
    [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    (edge : Finset V) (weight : (V → A) → M)
    (bound : OutsideAssignment (A := A) edge → M)
    (hbound : ∀ outside,
      (∑ inside : InsideAssignment (A := A) edge,
        weight (glue edge outside inside)) ≤ bound outside) :
    (∑ f : V → A, weight f) ≤ ∑ outside, bound outside := by
  rw [sum_univ_eq_sum_outside_inside edge weight]
  exact Finset.sum_le_sum fun outside _ ↦ hbound outside

/-- The inside fiber of an event after the outside assignment is exposed. -/
def eventFiber {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
    (edge : Finset V) (event : (V → A) → Prop) [DecidablePred event]
    (outside : OutsideAssignment (A := A) edge) :
    Finset (InsideAssignment (A := A) edge) :=
  Finset.univ.filter fun inside ↦ event (glue edge outside inside)

@[simp] lemma mem_eventFiber {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] (edge : Finset V) (event : (V → A) → Prop)
    [DecidablePred event]
    (outside : OutsideAssignment (A := A) edge)
    (inside : InsideAssignment (A := A) edge) :
    inside ∈ eventFiber edge event outside ↔ event (glue edge outside inside) := by
  classical
  simp [eventFiber]

/-- The number of global assignments satisfying an event is the sum of the
sizes of its inside fibers over all exposed outside assignments. -/
lemma card_event_eq_sum_fiber {V A : Type*}
    [Fintype V] [DecidableEq V] [Fintype A]
    (edge : Finset V) (event : (V → A) → Prop) [DecidablePred event] :
    ((Finset.univ : Finset (V → A)).filter event).card =
      ∑ outside : OutsideAssignment (A := A) edge,
        (eventFiber edge event outside).card := by
  classical
  calc
    ((Finset.univ : Finset (V → A)).filter event).card =
        ∑ f : V → A, if event f then 1 else 0 := by simp
    _ = ∑ outside : OutsideAssignment (A := A) edge,
          ∑ inside : InsideAssignment (A := A) edge,
            if event (glue edge outside inside) then 1 else 0 :=
      sum_univ_eq_sum_outside_inside edge (fun f ↦ if event f then 1 else 0)
    _ = ∑ outside : OutsideAssignment (A := A) edge,
          (eventFiber edge event outside).card := by
      apply Finset.sum_congr rfl
      intro outside _
      simp [eventFiber]

/-- Fiberwise cardinality bounds sum to a global cardinality bound. -/
lemma card_event_le_sum_of_fiber_bound {V A : Type*}
    [Fintype V] [DecidableEq V] [Fintype A]
    (edge : Finset V) (event : (V → A) → Prop)
    [DecidablePred event]
    (bound : OutsideAssignment (A := A) edge → ℕ)
    (hbound : ∀ outside, (eventFiber edge event outside).card ≤ bound outside) :
    ((Finset.univ : Finset (V → A)).filter event).card ≤
      ∑ outside, bound outside := by
  classical
  rw [card_event_eq_sum_fiber edge event]
  exact Finset.sum_le_sum fun outside _ ↦ hbound outside

/-- A constant fiber bound gives the usual product-space cardinality bound. -/
lemma card_event_le_card_outside_mul {V A : Type*}
    [Fintype V] [DecidableEq V] [Fintype A]
    (edge : Finset V) (event : (V → A) → Prop) (bound : ℕ)
    [DecidablePred event]
    (hbound : ∀ outside, (eventFiber edge event outside).card ≤ bound) :
    ((Finset.univ : Finset (V → A)).filter event).card ≤
      Fintype.card (OutsideAssignment (A := A) edge) * bound := by
  classical
  calc
    ((Finset.univ : Finset (V → A)).filter event).card ≤
        ∑ _outside : OutsideAssignment (A := A) edge, bound :=
      card_event_le_sum_of_fiber_bound edge event (fun _ ↦ bound) hbound
    _ = Fintype.card (OutsideAssignment (A := A) edge) * bound := by simp

/-- Uniform expectation also decomposes into an outside expectation followed
by an inside expectation. -/
lemma expect_eq_expect_outside_inside {V A M : Type*}
    [Fintype V] [DecidableEq V] [Fintype A]
    [AddCommMonoid M] [Module ℚ≥0 M]
    (edge : Finset V) (weight : (V → A) → M) :
    (𝔼 f : V → A, weight f) =
      𝔼 outside : OutsideAssignment (A := A) edge,
        𝔼 inside : InsideAssignment (A := A) edge,
          weight (glue edge outside inside) := by
  calc
    (𝔼 f : V → A, weight f) =
        𝔼 p : OutsideAssignment (A := A) edge × InsideAssignment (A := A) edge,
          weight ((exposureEquiv edge).symm p) := by
      apply Finset.expect_equiv (exposureEquiv edge)
      · simp
      · intro f _
        simp
    _ = 𝔼 outside : OutsideAssignment (A := A) edge,
          𝔼 inside : InsideAssignment (A := A) edge,
            weight (glue edge outside inside) := by
      simpa using (Finset.expect_product
        (Finset.univ : Finset (OutsideAssignment (A := A) edge))
        (Finset.univ : Finset (InsideAssignment (A := A) edge))
        (fun p ↦ weight ((exposureEquiv edge).symm p)))

/-- Indicator-event specialization of `expect_eq_expect_outside_inside`. -/
lemma expect_event_indicator_eq_expect_fiber {V A : Type*}
    [Fintype V] [DecidableEq V] [Fintype A]
    (edge : Finset V) (event : (V → A) → Prop) [DecidablePred event] :
    (𝔼 f : V → A, (if event f then 1 else 0 : ℚ)) =
      𝔼 outside : OutsideAssignment (A := A) edge,
        𝔼 inside : InsideAssignment (A := A) edge,
          (if event (glue edge outside inside) then 1 else 0 : ℚ) := by
  classical
  exact expect_eq_expect_outside_inside edge
    (fun f ↦ (if event f then 1 else 0 : ℚ))

/-- Short compatibility name for the rational indicator specialization. -/
alias expect_indicator_eq_expect_fiber := expect_event_indicator_eq_expect_fiber

/-- If every exposed fiber has indicator expectation at most `bound`, then
the global event has expectation at most the outside average of `bound`. -/
lemma expect_event_indicator_le_of_fiber_bound {V A : Type*}
    [Fintype V] [DecidableEq V] [Fintype A]
    (edge : Finset V) (event : (V → A) → Prop)
    [DecidablePred event]
    (bound : OutsideAssignment (A := A) edge → ℚ)
    (hbound : ∀ outside,
      (𝔼 inside : InsideAssignment (A := A) edge,
        (if event (glue edge outside inside) then 1 else 0 : ℚ)) ≤ bound outside) :
    (𝔼 f : V → A, (if event f then 1 else 0 : ℚ)) ≤
      𝔼 outside : OutsideAssignment (A := A) edge, bound outside := by
  classical
  rw [expect_event_indicator_eq_expect_fiber edge event]
  exact Finset.expect_le_expect fun outside _ ↦ hbound outside

/-- Short compatibility name for the fiberwise indicator bound. -/
alias expect_indicator_le_of_fiber_bound := expect_event_indicator_le_of_fiber_bound

end Erdos1027.FiniteExposure
