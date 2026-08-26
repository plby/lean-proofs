import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Finite Bonferroni inequalities

This file supplies the elementary finite inequality used when a sieve
Euler product is truncated after an even degree.  No probability space
is needed: everything is expressed as a finite subset sum.

For a finite set `s` and weights `x`, `elementarySymmetric s x k` is
the sum of `∏ i ∈ t, x i` over the `k`-element subsets `t ⊆ s`.
`bonferroniTruncation s x m` retains the terms of degrees `< m` in
the expansion of `∏ i ∈ s, (1 - x i)`.

The main application takes `m = 2 * R + 1`.  Since this is odd,
`bonferroni_even_upper` says that the truncation through degree `2 * R`
is an upper bound for the product.  The excess is at most the first
omitted elementary symmetric sum, and hence at most
`(∑ i ∈ s, x i) ^ m / m!`.
-/

namespace Erdos327.Analytic

open scoped BigOperators

open Finset

variable {ι : Type*}

/-- The `k`th elementary symmetric sum of `x` over the finite set `s`. -/
noncomputable def elementarySymmetric
    (s : Finset ι) (x : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ s.powersetCard k, ∏ i ∈ t, x i

/-- The expansion of `∏ i ∈ s, (1 - x i)` truncated before degree `m`. -/
noncomputable def bonferroniTruncation
    (s : Finset ι) (x : ι → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ range m, (-1 : ℝ) ^ k * elementarySymmetric s x k

/-- The signed error after truncating before degree `m`.

The sign is chosen so that this quantity is nonnegative when all
weights belong to `[0, 1]`.
-/
noncomputable def bonferroniRemainder
    (s : Finset ι) (x : ι → ℝ) (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ m *
    ((∏ i ∈ s, (1 - x i)) - bonferroniTruncation s x m)

@[simp] theorem elementarySymmetric_zero (s : Finset ι) (x : ι → ℝ) :
    elementarySymmetric s x 0 = 1 := by
  simp [elementarySymmetric]

@[simp] theorem elementarySymmetric_empty_succ (x : ι → ℝ) (k : ℕ) :
    elementarySymmetric ∅ x (k + 1) = 0 := by
  rw [elementarySymmetric]
  have hempty :
      (∅ : Finset ι).powersetCard (k + 1) = ∅ :=
    powersetCard_eq_empty.mpr (by simp)
  simp [hempty]

@[simp] theorem elementarySymmetric_empty (x : ι → ℝ) (k : ℕ) :
    elementarySymmetric ∅ x k = if k = 0 then 1 else 0 := by
  cases k <;> simp

/-- The elementary symmetric sums satisfy the usual insert recurrence. -/
theorem elementarySymmetric_insert_succ
    [DecidableEq ι] {a : ι} {s : Finset ι}
    (ha : a ∉ s) (x : ι → ℝ) (k : ℕ) :
    elementarySymmetric (insert a s) x (k + 1) =
      elementarySymmetric s x (k + 1) +
        x a * elementarySymmetric s x k := by
  classical
  rw [elementarySymmetric, elementarySymmetric,
    powersetCard_succ_insert ha, sum_union]
  · rw [sum_image]
    · simp only [Nat.succ_eq_add_one]
      rw [elementarySymmetric, mul_sum]
      congr 1
      apply sum_congr rfl
      intro u hu
      have hau : a ∉ u :=
        fun h ↦ ha ((mem_powersetCard.mp hu).1 h)
      rw [prod_insert hau]
    · intro u hu v hv huv
      have hau : a ∉ u :=
        fun h ↦ ha ((mem_powersetCard.mp hu).1 h)
      have hav : a ∉ v :=
        fun h ↦ ha ((mem_powersetCard.mp hv).1 h)
      have herase :=
        congrArg (fun q : Finset ι ↦ q.erase a) huv
      simpa [hau, hav] using herase
  · rw [disjoint_left]
    intro u hu hu'
    have hau : a ∉ u :=
      fun h ↦ ha ((mem_powersetCard.mp hu).1 h)
    rcases mem_image.mp hu' with ⟨v, _hv, rfl⟩
    exact hau (mem_insert_self _ _)

@[simp] theorem bonferroniTruncation_zero
    (s : Finset ι) (x : ι → ℝ) :
    bonferroniTruncation s x 0 = 0 := by
  simp [bonferroniTruncation]

theorem bonferroniTruncation_succ
    (s : Finset ι) (x : ι → ℝ) (m : ℕ) :
    bonferroniTruncation s x (m + 1) =
      bonferroniTruncation s x m +
        (-1 : ℝ) ^ m * elementarySymmetric s x m := by
  simp [bonferroniTruncation, sum_range_succ]

/-- Inserting one variable transforms a truncation of order `m + 1`
by subtracting that variable times the truncation of order `m`. -/
theorem bonferroniTruncation_insert_succ
    [DecidableEq ι] {a : ι} {s : Finset ι}
    (ha : a ∉ s) (x : ι → ℝ) (m : ℕ) :
    bonferroniTruncation (insert a s) x (m + 1) =
      bonferroniTruncation s x (m + 1) -
        x a * bonferroniTruncation s x m := by
  induction m with
  | zero =>
      simp [bonferroniTruncation_succ]
  | succ m ih =>
      rw [bonferroniTruncation_succ (insert a s) x (m + 1),
        bonferroniTruncation_succ s x (m + 1), ih,
        elementarySymmetric_insert_succ ha,
        bonferroniTruncation_succ s x m]
      ring

@[simp] theorem bonferroniTruncation_empty_succ
    (x : ι → ℝ) (m : ℕ) :
    bonferroniTruncation ∅ x (m + 1) = 1 := by
  induction m with
  | zero =>
      simp [bonferroniTruncation_succ]
  | succ m ih =>
      rw [bonferroniTruncation_succ]
      simp [ih]

@[simp] theorem bonferroniRemainder_zero
    (s : Finset ι) (x : ι → ℝ) :
    bonferroniRemainder s x 0 = ∏ i ∈ s, (1 - x i) := by
  simp [bonferroniRemainder]

/-- The signed remainder has a positive-coefficient insert recurrence. -/
theorem bonferroniRemainder_insert_succ
    [DecidableEq ι] {a : ι} {s : Finset ι}
    (ha : a ∉ s) (x : ι → ℝ) (m : ℕ) :
    bonferroniRemainder (insert a s) x (m + 1) =
      bonferroniRemainder s x (m + 1) +
        x a * bonferroniRemainder s x m := by
  classical
  rw [bonferroniRemainder, bonferroniRemainder,
    bonferroniRemainder, prod_insert ha,
    bonferroniTruncation_insert_succ ha]
  simp only [pow_succ]
  ring

/-- Every signed Bonferroni remainder lies between zero and the first
omitted elementary symmetric sum. -/
theorem bonferroniRemainder_nonneg_le
    (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hx1 : ∀ i ∈ s, x i ≤ 1) (m : ℕ) :
    0 ≤ bonferroniRemainder s x m ∧
      bonferroniRemainder s x m ≤ elementarySymmetric s x m := by
  classical
  induction s using Finset.induction generalizing m with
  | empty =>
      cases m with
      | zero => simp [bonferroniRemainder]
      | succ m =>
          simp [bonferroniRemainder]
  | @insert a s ha ih =>
      have hxa0 : 0 ≤ x a := hx0 a (mem_insert_self _ _)
      have hxa1 : x a ≤ 1 := hx1 a (mem_insert_self _ _)
      have hxs0 : ∀ i ∈ s, 0 ≤ x i :=
        fun i hi ↦ hx0 i (mem_insert_of_mem hi)
      have hxs1 : ∀ i ∈ s, x i ≤ 1 :=
        fun i hi ↦ hx1 i (mem_insert_of_mem hi)
      cases m with
      | zero =>
          simp only [bonferroniRemainder_zero,
            elementarySymmetric_zero]
          constructor
          · exact prod_nonneg fun i hi ↦ sub_nonneg.mpr
              (hx1 i hi)
          · exact prod_le_one
              (fun i hi ↦ sub_nonneg.mpr
                (hx1 i hi))
              (fun i hi ↦ sub_le_self _ (hx0 i hi))
      | succ m =>
          rw [bonferroniRemainder_insert_succ ha,
            elementarySymmetric_insert_succ ha]
          have hm := ih hxs0 hxs1 (m + 1)
          have hm' := ih hxs0 hxs1 m
          constructor
          · exact add_nonneg hm.1 (mul_nonneg hxa0 hm'.1)
          · exact add_le_add hm.2 (mul_le_mul_of_nonneg_left hm'.2 hxa0)

/-- The factorial-scaled elementary symmetric sum is bounded by the
corresponding power of the first symmetric sum. -/
theorem factorial_mul_elementarySymmetric_le_pow_sum
    (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (m : ℕ) :
    (m.factorial : ℝ) * elementarySymmetric s x m ≤
      (∑ i ∈ s, x i) ^ m := by
  classical
  induction s using Finset.induction generalizing m with
  | empty =>
      cases m <;> simp
  | @insert a s ha ih =>
      have hxa0 : 0 ≤ x a := hx0 a (mem_insert_self _ _)
      have hxs0 : ∀ i ∈ s, 0 ≤ x i :=
        fun i hi ↦ hx0 i (mem_insert_of_mem hi)
      have hsum0 : 0 ≤ ∑ i ∈ s, x i :=
        sum_nonneg fun i hi ↦ hxs0 i hi
      cases m with
      | zero => simp
      | succ m =>
          rw [elementarySymmetric_insert_succ ha, sum_insert ha]
          calc
            ((m + 1).factorial : ℝ) *
                  (elementarySymmetric s x (m + 1) +
                    x a * elementarySymmetric s x m) =
                ((m + 1).factorial : ℝ) *
                    elementarySymmetric s x (m + 1) +
                  (m + 1 : ℝ) * x a *
                    ((m.factorial : ℝ) *
                      elementarySymmetric s x m) := by
                simp only [Nat.factorial_succ, Nat.cast_mul,
                  Nat.cast_add, Nat.cast_one]
                ring
            _ ≤ (∑ i ∈ s, x i) ^ (m + 1) +
                  (m + 1 : ℝ) * x a *
                    (∑ i ∈ s, x i) ^ m := by
                gcongr
                · exact ih hxs0 (m + 1)
                · exact ih hxs0 m
            _ ≤ (x a + ∑ i ∈ s, x i) ^ (m + 1) := by
                have hbern :=
                  pow_add_mul_le_add_pow
                    (a := ∑ i ∈ s, x i) (b := x a)
                    hsum0 (by positivity) (m + 1)
                simpa [Nat.succ_sub_one, add_comm, mul_comm,
                  mul_left_comm, mul_assoc] using hbern

/-- The first omitted elementary symmetric sum admits the standard
exponential-series bound. -/
theorem elementarySymmetric_le_pow_sum_div_factorial
    (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (m : ℕ) :
    elementarySymmetric s x m ≤
      (∑ i ∈ s, x i) ^ m / (m.factorial : ℝ) := by
  rw [le_div_iff₀]
  · simpa [mul_comm] using
      factorial_mul_elementarySymmetric_le_pow_sum s x hx0 m
  · positivity

/-- The finite even Bonferroni inequality: truncating after degree
`2 * R` gives an upper bound for the product. -/
theorem bonferroni_even_upper
    (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hx1 : ∀ i ∈ s, x i ≤ 1) (R : ℕ) :
    (∏ i ∈ s, (1 - x i)) ≤
      bonferroniTruncation s x (2 * R + 1) := by
  have h :=
    (bonferroniRemainder_nonneg_le s x hx0 hx1 (2 * R + 1)).1
  have hsign : (-1 : ℝ) ^ (2 * R + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [bonferroniRemainder, hsign] at h
  linarith

/-- The excess in the even Bonferroni upper bound is controlled by
the first omitted elementary symmetric sum. -/
theorem bonferroni_even_error_le_elementarySymmetric
    (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hx1 : ∀ i ∈ s, x i ≤ 1) (R : ℕ) :
    bonferroniTruncation s x (2 * R + 1) -
        (∏ i ∈ s, (1 - x i)) ≤
      elementarySymmetric s x (2 * R + 1) := by
  have h :=
    (bonferroniRemainder_nonneg_le s x hx0 hx1 (2 * R + 1)).2
  have hsign : (-1 : ℝ) ^ (2 * R + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [bonferroniRemainder, hsign] at h
  linarith

/-- Complete numerical error estimate for the finite even Bonferroni
upper bound.

To instantiate this in a weighted sieve, take `s` to be the finite set
of local primes, put the local density at `p` in `x p`, and choose `R`
so that the displayed exponential-series tail is within the desired
error budget.
-/
theorem bonferroni_even_error_le_pow_sum_div_factorial
    (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hx1 : ∀ i ∈ s, x i ≤ 1) (R : ℕ) :
    bonferroniTruncation s x (2 * R + 1) -
        (∏ i ∈ s, (1 - x i)) ≤
      (∑ i ∈ s, x i) ^ (2 * R + 1) /
        ((2 * R + 1).factorial : ℝ) :=
  (bonferroni_even_error_le_elementarySymmetric s x hx0 hx1 R).trans
    (elementarySymmetric_le_pow_sum_div_factorial
      s x hx0 (2 * R + 1))

end Erdos327.Analytic
