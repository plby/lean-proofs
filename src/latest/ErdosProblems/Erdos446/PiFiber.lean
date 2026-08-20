/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SlotConfigurations

/-!
# Erdős Problem 446: splitting one coordinate of a finite dependent product

Ford's distinguished-prime argument fixes every prime coordinate but one and
sums over the remaining prime.  The elementary equivalence and weighted fiber
estimate below isolate that operation for arbitrary finite dependent products.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- A dependent array with coordinate `i` omitted. -/
abbrev PiAway {I : Type*} (A : I → Type*) (i : I) :=
  ∀ j : {j : I // j ≠ i}, A j.1

/-- Insert one coordinate into an array indexed away from it. -/
def piInsert {I : Type*} [DecidableEq I] {A : I → Type*} (i : I)
    (x : A i) (v : PiAway A i) : ∀ j, A j := fun j ↦ by
  by_cases h : j = i
  · subst j
    exact x
  · exact v ⟨j, h⟩

@[simp]
theorem piInsert_same {I : Type*} [DecidableEq I] {A : I → Type*}
    (i : I) (x : A i) (v : PiAway A i) : piInsert i x v i = x := by
  simp [piInsert]

@[simp]
theorem piInsert_ne {I : Type*} [DecidableEq I] {A : I → Type*}
    (i : I) (x : A i) (v : PiAway A i) (j : I) (hji : j ≠ i) :
    piInsert i x v j = v ⟨j, hji⟩ := by
  simp [piInsert, hji]

/-- Split a dependent function into its value at `i` and all other values. -/
def piSplitAt {I : Type*} [DecidableEq I] (A : I → Type*) (i : I) :
    (∀ j, A j) ≃ A i × PiAway A i where
  toFun v := (v i, fun j ↦ v j.1)
  invFun p := piInsert i p.1 p.2
  left_inv v := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [piInsert, h]
  right_inv p := by
    apply Prod.ext
    · simp
    · funext j
      simp [piInsert, j.2]

theorem prod_piInsert {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} {R : Type*} [CommMonoid R]
    (w : ∀ i, A i → R) (i : I)
    (x : A i) (v : PiAway A i) :
    (∏ j, w j (piInsert i x v j)) =
      w i x * ∏ j : {j : I // j ≠ i}, w j.1 (v j) := by
  classical
  rw [Fintype.prod_eq_mul_prod_subtype_ne]
  rw [piInsert_same]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact congrArg (w j.1) (piInsert_ne i x v j.1 j.2)

/-- Sum a nonnegative product weight fiberwise in one distinguished
coordinate. -/
theorem sum_pi_event_weight_le_fiber
    {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)]
    (w : ∀ i, A i → ℝ) (hw : ∀ i x, 0 ≤ w i x)
    (i : I) (P : (∀ j, A j) → Prop) [DecidablePred P]
    (C : ℝ)
    (hfiber : ∀ v : PiAway A i,
      (∑ x : A i, if P (piInsert i x v) then w i x else 0) ≤ C) :
    (∑ a : ∀ j, A j, if P a then ∏ j, w j (a j) else 0) ≤
      ∑ v : PiAway A i,
        (∏ j, w j.1 (v j)) * C := by
  classical
  rw [Fintype.sum_equiv (piSplitAt A i)
    (fun a : ∀ j, A j ↦ if P a then ∏ j, w j (a j) else 0)
    (fun p : A i × PiAway A i ↦
      if P (piInsert i p.1 p.2) then
        ∏ j, w j (piInsert i p.1 p.2 j) else 0) (fun a ↦ by
          rw [show piInsert i ((piSplitAt A i a).1)
              ((piSplitAt A i a).2) = a from
            (piSplitAt A i).left_inv a])]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro v hv
  calc
    (∑ x : A i, if P (piInsert i x v) then
        ∏ j, w j (piInsert i x v j) else 0) =
        (∏ j, w j.1 (v j)) *
          ∑ x : A i, if P (piInsert i x v) then w i x else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [prod_piInsert]
      by_cases hP : P (piInsert i x v) <;> simp [hP]
      ring
    _ ≤ (∏ j, w j.1 (v j)) * C := by
      exact mul_le_mul_of_nonneg_left (hfiber v)
        (Finset.prod_nonneg fun j hj ↦ hw j.1 (v j))

end Erdos446
