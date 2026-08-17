/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos807.HostMoments
import ErdosProblems.Erdos807.ModerateMoments

/-!
# Finite overlap-range decompositions

This file isolates the elementary range bookkeeping needed when the template
order `k` is divisible by ten.  The exact partition has five pieces:

* `i = 0`;
* `i = 1`;
* `2 ≤ i ≤ 9k/10`;
* `9k/10 < i < k`; and
* `i = k`.

For the large-overlap piece the defect coordinate is `j = k - i`.  Notice the
important endpoint: the *exact* image of the strict large range is
`1 ≤ j ≤ k/10 - 1`.  The commonly used range `1 ≤ j ≤ k/10` has one
extra endpoint, corresponding to `i = 9k/10`; below we also prove the padded
upper bound into that larger range for nonnegative summands.
-/

open scoped BigOperators

namespace Erdos807
namespace MomentRanges

open Finset

/-- The moderate intersection sizes. -/
def moderateRange (k : ℕ) : Finset ℕ := Icc 2 (9 * k / 10)

/-- The strict large-overlap intersection sizes. -/
def largeOverlapRange (k : ℕ) : Finset ℕ :=
  (range k).filter fun i ↦ 9 * k / 10 < i

/-- The padded range of large-overlap defects used in estimates. -/
def largeDefectRange (k : ℕ) : Finset ℕ := Icc 1 (k / 10)

/-- The exact range of defects corresponding to strict large overlaps. -/
def exactLargeDefectRange (k : ℕ) : Finset ℕ := Icc 1 (k / 10 - 1)

@[simp] theorem mem_moderateRange {k i : ℕ} :
    i ∈ moderateRange k ↔ 2 ≤ i ∧ i ≤ 9 * k / 10 := by
  simp [moderateRange]

@[simp] theorem mem_largeOverlapRange {k i : ℕ} :
    i ∈ largeOverlapRange k ↔ 9 * k / 10 < i ∧ i < k := by
  simp [largeOverlapRange, and_comm]

@[simp] theorem mem_largeDefectRange {k j : ℕ} :
    j ∈ largeDefectRange k ↔ 1 ≤ j ∧ j ≤ k / 10 := by
  simp [largeDefectRange]

@[simp] theorem mem_exactLargeDefectRange {k j : ℕ} :
    j ∈ exactLargeDefectRange k ↔
      1 ≤ j ∧ j ≤ k / 10 - 1 := by
  simp [exactLargeDefectRange]

/-- Divisibility by ten gives the exact complementary-cutoff identity. -/
theorem nine_tenths_add_one_tenth {k : ℕ} (hdiv : 10 ∣ k) :
    9 * k / 10 + k / 10 = k := by
  obtain ⟨t, rfl⟩ := hdiv
  have h9 : 9 * (10 * t) / 10 = 9 * t := by
    rw [show 9 * (10 * t) = (9 * t) * 10 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  have h1 : 10 * t / 10 = t := Nat.mul_div_cancel_left _ (by norm_num)
  rw [h9, h1]
  ring

/-- Peel the two small endpoints and the top endpoint off `range (k+1)`. -/
theorem sum_range_eq_zero_one_middle_top
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) {k : ℕ} (hk : 2 ≤ k) :
    (∑ i ∈ range (k + 1), f i) =
      f 0 + f 1 + (∑ i ∈ Icc 2 (k - 1), f i) + f k := by
  have hrange : range (k + 1) =
      insert 0 (insert 1 (Icc 2 (k - 1) ∪ {k})) := by
    ext i
    simp only [mem_range, mem_insert, mem_union, mem_Icc, mem_singleton]
    omega
  have h0 : 0 ∉ insert 1 (Icc 2 (k - 1) ∪ {k}) := by
    simp only [mem_insert, mem_union, mem_Icc, mem_singleton, not_or]
    omega
  have h1 : 1 ∉ Icc 2 (k - 1) ∪ {k} := by
    simp only [mem_union, mem_Icc, mem_singleton, not_or]
    omega
  have hdis : Disjoint (Icc 2 (k - 1)) ({k} : Finset ℕ) := by
    rw [disjoint_left]
    intro i hi hik
    simp only [mem_Icc] at hi
    simp only [mem_singleton] at hik
    omega
  rw [hrange, sum_insert h0, sum_insert h1, sum_union hdis, sum_singleton]
  ac_rfl

/-- The middle interval is the disjoint union of the moderate and strict
large-overlap ranges. -/
theorem Icc_two_pred_eq_moderate_union_large {k : ℕ} (hk : 10 ≤ k) :
    Icc 2 (k - 1) = moderateRange k ∪ largeOverlapRange k := by
  have hm : 2 ≤ 9 * k / 10 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 10)).2
    nlinarith
  ext i
  simp only [mem_Icc, mem_union, mem_moderateRange, mem_largeOverlapRange]
  omega

theorem disjoint_moderateRange_largeOverlapRange (k : ℕ) :
    Disjoint (moderateRange k) (largeOverlapRange k) := by
  rw [disjoint_left]
  intro i hiM hiL
  rw [mem_moderateRange] at hiM
  rw [mem_largeOverlapRange] at hiL
  omega

/-- Exact five-piece decomposition of the overlap sum. -/
theorem sum_range_eq_five_ranges
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) {k : ℕ} (hk : 10 ≤ k) :
    (∑ i ∈ range (k + 1), f i) =
      f 0 + f 1 +
        (∑ i ∈ moderateRange k, f i) +
        (∑ i ∈ largeOverlapRange k, f i) + f k := by
  rw [sum_range_eq_zero_one_middle_top f (by omega),
    Icc_two_pred_eq_moderate_union_large hk,
    sum_union (disjoint_moderateRange_largeOverlapRange k)]
  ac_rfl

/-- Reflection `i ↦ k-i` is an exact reindexing of the strict large range by
the nonzero defects strictly below `k/10`. -/
theorem sum_largeOverlapRange_eq_sum_exactLargeDefectRange
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) {k : ℕ} (hdiv : 10 ∣ k) :
    (∑ i ∈ largeOverlapRange k, f i) =
      ∑ j ∈ exactLargeDefectRange k, f (k - j) := by
  classical
  have hcut := nine_tenths_add_one_tenth hdiv
  apply Finset.sum_bij (fun i _ ↦ k - i)
  · intro i hi
    rw [mem_largeOverlapRange] at hi
    rw [mem_exactLargeDefectRange]
    omega
  · intro i₁ hi₁ i₂ hi₂ heq
    rw [mem_largeOverlapRange] at hi₁ hi₂
    omega
  · intro j hj
    rw [mem_exactLargeDefectRange] at hj
    refine ⟨k - j, ?_, ?_⟩
    · rw [mem_largeOverlapRange]
      omega
    · omega
  · intro i hi
    rw [mem_largeOverlapRange] at hi
    congr 1
    omega

/-- The exact defect range is contained in the padded range used by the
analytic large-overlap estimate. -/
theorem exactLargeDefectRange_subset_largeDefectRange (k : ℕ) :
    exactLargeDefectRange k ⊆ largeDefectRange k := by
  intro j hj
  rw [mem_exactLargeDefectRange] at hj
  rw [mem_largeDefectRange]
  omega

/-- For nonnegative real summands the strict large-overlap sum is bounded by
the customary padded defect sum `1 ≤ j ≤ k/10`. -/
theorem sum_largeOverlapRange_le_sum_largeDefectRange
    (f : ℕ → ℝ) {k : ℕ} (hdiv : 10 ∣ k)
    (hf : ∀ j ∈ largeDefectRange k, 0 ≤ f (k - j)) :
    (∑ i ∈ largeOverlapRange k, f i) ≤
      ∑ j ∈ largeDefectRange k, f (k - j) := by
  rw [sum_largeOverlapRange_eq_sum_exactLargeDefectRange f hdiv]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (exactLargeDefectRange_subset_largeDefectRange k)
  intro j hj _hjExact
  exact hf j hj

/-- Exact five-piece identity with the strict large range already expressed
in the defect coordinate. -/
theorem sum_range_eq_zero_one_moderate_exactDefect_top
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) {k : ℕ}
    (hk : 10 ≤ k) (hdiv : 10 ∣ k) :
    (∑ i ∈ range (k + 1), f i) =
      f 0 + f 1 +
        (∑ i ∈ moderateRange k, f i) +
        (∑ j ∈ exactLargeDefectRange k, f (k - j)) + f k := by
  rw [sum_range_eq_five_ranges f hk,
    sum_largeOverlapRange_eq_sum_exactLargeDefectRange f hdiv]

/-- Padded real-valued version used to combine nonnegative moment bounds. -/
theorem sum_range_le_zero_one_moderate_largeDefect_top
    (f : ℕ → ℝ) {k : ℕ} (hk : 10 ≤ k) (hdiv : 10 ∣ k)
    (hf : ∀ j ∈ largeDefectRange k, 0 ≤ f (k - j)) :
    (∑ i ∈ range (k + 1), f i) ≤
      f 0 + f 1 +
        (∑ i ∈ moderateRange k, f i) +
        (∑ j ∈ largeDefectRange k, f (k - j)) + f k := by
  rw [sum_range_eq_five_ranges f hk]
  gcongr
  exact sum_largeOverlapRange_le_sum_largeDefectRange f hdiv hf

end MomentRanges
end Erdos807
