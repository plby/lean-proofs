/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# Finite degree buckets for Erdős Problem 636

This file records the elementary one-shot bucketing argument used before
the crowd/switching construction.  If a natural-valued statistic is bounded
by `B` on a finite family, division into intervals of width `w` gives
`B / w + 1` possible cells.  A largest fibre contains at least the average
number of elements, with division cleared from the conclusion.
-/

namespace Erdos636

noncomputable section

universe u v

variable {α : Type u} {β : Type v} [DecidableEq β]

/-- A largest fibre of a map into a nonempty finite target contains at least
the average number of source elements.  The conclusion is cross-multiplied,
so it has no divisibility or rounding side conditions. -/
theorem exists_fiber_card_mul_ge_of_mapsTo
    (M : Finset α) (T : Finset β) (f : α → β)
    (hT : T.Nonempty) (hmaps : ∀ x ∈ M, f x ∈ T) :
    ∃ q ∈ T, M.card ≤ (M.filter fun x ↦ f x = q).card * T.card := by
  classical
  obtain ⟨q, hq, hmax⟩ :=
    Finset.exists_max_image T (fun q ↦ (M.filter fun x ↦ f x = q).card) hT
  refine ⟨q, hq, ?_⟩
  calc
    M.card = ∑ y ∈ T, (M.filter fun x ↦ f x = y).card := by
      exact Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _y ∈ T, (M.filter fun x ↦ f x = q).card := by
      exact Finset.sum_le_sum fun y hy ↦ hmax y hy
    _ = (M.filter fun x ↦ f x = q).card * T.card := by
      simp [Nat.mul_comm]

/-- A bounded natural-valued statistic has a large subfamily contained in
one interval of width `w`.

The chosen family `X` is a subset of `M`; any two of its values have natural
distance strictly less than `w`; and `M.card ≤ X.card * (B / w + 1)`.
The final inequality is the exact finite pigeonhole bound. -/
theorem exists_large_nat_degree_bucket
    (M : Finset α) (f : α → ℕ) (B w : ℕ) (hw : 0 < w)
    (hbound : ∀ x ∈ M, f x ≤ B) :
    ∃ X : Finset α,
      X ⊆ M ∧
      M.card ≤ X.card * (B / w + 1) ∧
      ∀ x ∈ X, ∀ y ∈ X,
        |(((f x : ℕ) : ℝ) - ((f y : ℕ) : ℝ))| < (w : ℝ) := by
  classical
  have hmaps : ∀ x ∈ M, f x / w ∈ Finset.range (B / w + 1) := by
    intro x hx
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right (hbound x hx)
  obtain ⟨q, hq, hcard⟩ :=
    exists_fiber_card_mul_ge_of_mapsTo M (Finset.range (B / w + 1))
      (fun x ↦ f x / w) (by simp) hmaps
  let X := M.filter fun x ↦ f x / w = q
  refine ⟨X, Finset.filter_subset _ _, ?_, ?_⟩
  · simpa [X] using hcard
  · intro x hx y hy
    have hxq : f x / w = q := (Finset.mem_filter.mp hx).2
    have hyq : f y / w = q := (Finset.mem_filter.mp hy).2
    have hxmod : f x % w < w := Nat.mod_lt _ hw
    have hymod : f y % w < w := Nat.mod_lt _ hw
    have hxsplit : w * (f x / w) + f x % w = f x := Nat.div_add_mod _ _
    have hysplit : w * (f y / w) + f y % w = f y := Nat.div_add_mod _ _
    rw [hxq] at hxsplit
    rw [hyq] at hysplit
    have hxy : f x < f y + w ∧ f y < f x + w := by omega
    have hxyR : (f x : ℝ) < (f y : ℝ) + w := by exact_mod_cast hxy.1
    have hyxR : (f y : ℝ) < (f x : ℝ) + w := by exact_mod_cast hxy.2
    rw [abs_lt]
    constructor <;> linarith

end

end Erdos636
