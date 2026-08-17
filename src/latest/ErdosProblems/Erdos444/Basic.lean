/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# Erdős Problem 444: elementary definitions

This file gives literal finite-set definitions for the quantities in the
problem.  The public cutoff is real: `positiveBelow x` is exactly the set of
positive natural numbers in the half-open interval `[1, x)`.  Natural-cutoff
variants are provided for the discrete number-theoretic argument.
-/

open Filter
open scoped BigOperators

namespace Erdos444

/-- The positive natural numbers in the real half-open interval `[1, x)`. -/
noncomputable def positiveBelow (x : ℝ) : Finset ℕ :=
  Finset.Ico 1 ⌈x⌉₊

/-- The positive natural numbers in the natural half-open interval `[1, x)`. -/
def positiveBelowNat (x : ℕ) : Finset ℕ :=
  Finset.Ico 1 x

@[simp]
lemma mem_positiveBelow_iff {x : ℝ} {n : ℕ} :
    n ∈ positiveBelow x ↔ 1 ≤ n ∧ (n : ℝ) < x := by
  simp [positiveBelow, Nat.lt_ceil]

@[simp]
lemma mem_positiveBelowNat_iff {x n : ℕ} :
    n ∈ positiveBelowNat x ↔ 1 ≤ n ∧ n < x := by
  simp [positiveBelowNat]

@[simp]
lemma positiveBelow_natCast (x : ℕ) :
    positiveBelow (x : ℝ) = positiveBelowNat x := by
  simp [positiveBelow, positiveBelowNat]

lemma positiveBelow_mono : Monotone positiveBelow := by
  intro x y hxy
  exact Finset.Ico_subset_Ico le_rfl (Nat.ceil_mono hxy)

lemma positiveBelowNat_mono : Monotone positiveBelowNat := by
  intro x y hxy
  exact Finset.Ico_subset_Ico le_rfl hxy

/-- `d_A(n)`, the number of positive members of `A` dividing `n`.

Mathlib's `Nat.divisors 0` is empty.  All maxima below are over positive `n`,
so this convention affects no value occurring in Problem 444.
-/
noncomputable def divisorCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact (n.divisors.filter fun d ↦ d ∈ A).card

@[simp]
lemma divisorCount_zero (A : Set ℕ) : divisorCount A 0 = 0 := by
  classical
  simp [divisorCount]

lemma divisorCount_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ divisorCount A n :=
  Nat.zero_le _

lemma divisorCount_le_card_divisors (A : Set ℕ) (n : ℕ) :
    divisorCount A n ≤ n.divisors.card := by
  classical
  exact Finset.card_filter_le _ _

lemma divisorCount_mono_set {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    divisorCount A n ≤ divisorCount B n := by
  classical
  apply Finset.card_le_card
  intro d hd
  simp only [Finset.mem_filter] at hd ⊢
  exact ⟨hd.1, hAB hd.2⟩

/-- Every member of a finite positive subset of `A` divides its product. -/
lemma card_le_divisorCount_prod (A : Set ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a ∈ A ∧ a ≠ 0) :
    S.card ≤ divisorCount A (∏ a ∈ S, a) := by
  classical
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter]
  refine ⟨Nat.mem_divisors.mpr ⟨?_, ?_⟩, (hS a ha).1⟩
  · exact Finset.dvd_prod_of_mem id ha
  · exact Finset.prod_ne_zero_iff.mpr fun b hb ↦ (hS b hb).2

/-- The maximum of `d_A(n)` over positive natural `n < x`, for real `x`. -/
noncomputable def maxDivisorCount (A : Set ℕ) (x : ℝ) : ℕ :=
  (positiveBelow x).sup (divisorCount A)

/-- The maximum of `d_A(n)` over positive natural `n < x`, for natural `x`. -/
noncomputable def maxDivisorCountNat (A : Set ℕ) (x : ℕ) : ℕ :=
  (positiveBelowNat x).sup (divisorCount A)

@[simp]
lemma maxDivisorCount_natCast (A : Set ℕ) (x : ℕ) :
    maxDivisorCount A (x : ℝ) = maxDivisorCountNat A x := by
  simp [maxDivisorCount, maxDivisorCountNat]

lemma divisorCount_le_maxDivisorCount {A : Set ℕ} {n : ℕ} {x : ℝ}
    (hn : 1 ≤ n) (hnx : (n : ℝ) < x) :
    divisorCount A n ≤ maxDivisorCount A x := by
  exact Finset.le_sup (mem_positiveBelow_iff.mpr ⟨hn, hnx⟩)

lemma divisorCount_le_maxDivisorCountNat {A : Set ℕ} {n x : ℕ}
    (hn : 1 ≤ n) (hnx : n < x) :
    divisorCount A n ≤ maxDivisorCountNat A x := by
  exact Finset.le_sup (mem_positiveBelowNat_iff.mpr ⟨hn, hnx⟩)

lemma maxDivisorCount_le {A : Set ℕ} {x : ℝ} {m : ℕ}
    (h : ∀ n : ℕ, 1 ≤ n → (n : ℝ) < x → divisorCount A n ≤ m) :
    maxDivisorCount A x ≤ m := by
  apply Finset.sup_le
  intro n hn
  exact h n (mem_positiveBelow_iff.mp hn).1 (mem_positiveBelow_iff.mp hn).2

lemma maxDivisorCountNat_le {A : Set ℕ} {x m : ℕ}
    (h : ∀ n : ℕ, 1 ≤ n → n < x → divisorCount A n ≤ m) :
    maxDivisorCountNat A x ≤ m := by
  apply Finset.sup_le
  intro n hn
  exact h n (mem_positiveBelowNat_iff.mp hn).1 (mem_positiveBelowNat_iff.mp hn).2

lemma maxDivisorCount_mono (A : Set ℕ) : Monotone (maxDivisorCount A) := by
  intro x y hxy
  exact Finset.sup_mono (positiveBelow_mono hxy)

lemma maxDivisorCountNat_mono (A : Set ℕ) : Monotone (maxDivisorCountNat A) := by
  intro x y hxy
  exact Finset.sup_mono (positiveBelowNat_mono hxy)

lemma maxDivisorCount_nonneg (A : Set ℕ) (x : ℝ) :
    0 ≤ maxDivisorCount A x :=
  Nat.zero_le _

lemma maxDivisorCountNat_nonneg (A : Set ℕ) (x : ℕ) :
    0 ≤ maxDivisorCountNat A x :=
  Nat.zero_le _

/-- The reciprocal mass of `A ∩ [1,x)`, for real `x`. -/
noncomputable def reciprocalMass (A : Set ℕ) (x : ℝ) : ℝ := by
  classical
  exact ∑ a ∈ (positiveBelow x).filter (fun a ↦ a ∈ A), (a : ℝ)⁻¹

/-- The reciprocal mass of `A ∩ [1,x)`, for natural `x`. -/
noncomputable def reciprocalMassNat (A : Set ℕ) (x : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ (positiveBelowNat x).filter (fun a ↦ a ∈ A), (a : ℝ)⁻¹

@[simp]
lemma reciprocalMass_natCast (A : Set ℕ) (x : ℕ) :
    reciprocalMass A (x : ℝ) = reciprocalMassNat A x := by
  classical
  simp [reciprocalMass, reciprocalMassNat]

lemma reciprocalMass_nonneg (A : Set ℕ) (x : ℝ) :
    0 ≤ reciprocalMass A x := by
  classical
  apply Finset.sum_nonneg
  intro a ha
  exact inv_nonneg.mpr (Nat.cast_nonneg a)

lemma reciprocalMassNat_nonneg (A : Set ℕ) (x : ℕ) :
    0 ≤ reciprocalMassNat A x := by
  classical
  apply Finset.sum_nonneg
  intro a ha
  exact inv_nonneg.mpr (Nat.cast_nonneg a)

lemma reciprocalMass_mono (A : Set ℕ) : Monotone (reciprocalMass A) := by
  classical
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨positiveBelow_mono hxy ha.1, ha.2⟩
  · intro a ha hnot
    exact inv_nonneg.mpr (Nat.cast_nonneg a)

lemma reciprocalMassNat_mono (A : Set ℕ) : Monotone (reciprocalMassNat A) := by
  classical
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨positiveBelowNat_mono hxy ha.1, ha.2⟩
  · intro a ha hnot
    exact inv_nonneg.mpr (Nat.cast_nonneg a)

lemma reciprocalMass_pos_of_mem {A : Set ℕ} {a : ℕ} (haA : a ∈ A)
    (ha : 0 < a) {x : ℝ} (hax : (a : ℝ) < x) :
    0 < reciprocalMass A x := by
  classical
  apply Finset.sum_pos
  · intro n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one
      (mem_positiveBelow_iff.mp (Finset.mem_filter.mp hn).1).1
    exact inv_pos.mpr (Nat.cast_pos.mpr hnpos)
  · refine ⟨a, ?_⟩
    simp only [Finset.mem_filter, mem_positiveBelow_iff]
    exact ⟨⟨ha, hax⟩, haA⟩

lemma reciprocalMassNat_pos_of_mem {A : Set ℕ} {a : ℕ} (haA : a ∈ A)
    (ha : 0 < a) {x : ℕ} (hax : a < x) :
    0 < reciprocalMassNat A x := by
  simpa using reciprocalMass_pos_of_mem haA ha (x := (x : ℝ)) (by exact_mod_cast hax)

lemma eventually_reciprocalMass_pos {A : Set ℕ} (hA : A.Infinite) :
    ∀ᶠ x in (atTop : Filter ℝ), 0 < reciprocalMass A x := by
  obtain ⟨a, haA, ha⟩ := hA.exists_gt 0
  filter_upwards [eventually_gt_atTop (a : ℝ)] with x hx
  exact reciprocalMass_pos_of_mem haA ha hx

lemma eventually_reciprocalMassNat_pos {A : Set ℕ} (hA : A.Infinite) :
    ∀ᶠ x in (atTop : Filter ℕ), 0 < reciprocalMassNat A x := by
  obtain ⟨a, haA, ha⟩ := hA.exists_gt 0
  filter_upwards [eventually_gt_atTop a] with x hx
  exact reciprocalMassNat_pos_of_mem haA ha hx

/-- The ratio in Problem 444, computed in `ℝ` before passage to `EReal`. -/
noncomputable def ratio (A : Set ℕ) (k : ℕ) (x : ℝ) : ℝ :=
  (maxDivisorCount A x : ℝ) / (reciprocalMass A x) ^ k

/-- The natural-cutoff form of the ratio in Problem 444. -/
noncomputable def ratioNat (A : Set ℕ) (k x : ℕ) : ℝ :=
  (maxDivisorCountNat A x : ℝ) / (reciprocalMassNat A x) ^ k

@[simp]
lemma ratio_natCast (A : Set ℕ) (k x : ℕ) :
    ratio A k (x : ℝ) = ratioNat A k x := by
  simp [ratio, ratioNat]

lemma ratio_nonneg (A : Set ℕ) (k : ℕ) (x : ℝ) :
    0 ≤ ratio A k x := by
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (reciprocalMass_nonneg A x) k)

lemma ratioNat_nonneg (A : Set ℕ) (k x : ℕ) :
    0 ≤ ratioNat A k x := by
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (reciprocalMassNat_nonneg A x) k)

/-- A real-valued function is unbounded on every tail of its domain. -/
def tailUnbounded {α : Type*} [Preorder α] (f : α → ℝ) : Prop :=
  ∀ C : ℝ, ∀ X : α, ∃ x : α, X ≤ x ∧ C < f x

/-- Tail-unbounded real functions have `EReal` limsup equal to `⊤`. -/
theorem limsup_coe_eq_top_of_tailUnbounded {α : Type*} [Preorder α]
    [Nonempty α] [IsDirectedOrder α] (f : α → ℝ) (hf : tailUnbounded f) :
    atTop.limsup (fun x ↦ (f x : EReal)) = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro C
  have hfreq : ∃ᶠ x in atTop, ((C + 1 : ℝ) : EReal) ≤ (f x : EReal) := by
    rw [frequently_atTop]
    intro X
    obtain ⟨x, hXx, hx⟩ := hf (C + 1) X
    exact ⟨x, hXx, EReal.coe_le_coe_iff.mpr hx.le⟩
  refine lt_of_lt_of_le ?_ (le_limsup_of_frequently_le' hfreq)
  exact EReal.coe_lt_coe_iff.mpr (by linarith)

end Erdos444
