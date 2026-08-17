/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos877.Enumeration
import ErdosProblems.Erdos877.DoubleCount
import ErdosProblems.Erdos877.Binomial
import ErdosProblems.Erdos877.Asymptotic

/-!
# Erdős 877: the final counting argument

This file combines the enumeration of all sum-free cores with the
Łuczak--Schoen deletion double count.  Small maximal sum-free sets are counted
directly by a lower Boolean-lattice layer.  Large maximal sum-free sets gain
more binary digits from their many good deletions than are lost when the
deleted elements are reconstructed.
-/

open Filter Finset
open scoped Topology

namespace Erdos877

/-- Maximal sum-free subsets of `[1,n]` having cardinality less than `n / 10`
in the division-free form convenient for partitioning the finite family. -/
noncomputable def smallMaximalSumFreeSets (n : ℕ) : Finset (Finset ℕ) :=
  (maximalSumFreeSets n).filter fun A ↦ 10 * A.card < n

@[simp] theorem mem_smallMaximalSumFreeSets {n : ℕ} {A : Finset ℕ} :
    A ∈ smallMaximalSumFreeSets n ↔
      MaximalSumFreeIn (interval n) A ∧ 10 * A.card < n := by
  classical
  simp [smallMaximalSumFreeSets]

/-- The small and large subfamilies partition all maximal sum-free sets. -/
theorem small_union_large (n : ℕ) :
    smallMaximalSumFreeSets n ∪ largeMaximalSumFreeSets n =
      maximalSumFreeSets n := by
  classical
  ext A
  simp only [Finset.mem_union, mem_smallMaximalSumFreeSets,
    mem_largeMaximalSumFreeSets, mem_maximalSumFreeSets]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    rcases lt_or_ge (10 * A.card) n with hs | hl
    · exact Or.inl ⟨h, hs⟩
    · exact Or.inr ⟨h, hl⟩

theorem disjoint_small_large (n : ℕ) :
    Disjoint (smallMaximalSumFreeSets n) (largeMaximalSumFreeSets n) := by
  classical
  rw [Finset.disjoint_left]
  intro A hsmall hlarge
  have hs := (mem_smallMaximalSumFreeSets.mp hsmall).2
  have hl := (mem_largeMaximalSumFreeSets.mp hlarge).2
  omega

/-- Exact decomposition of the maximal sum-free count. -/
theorem maximalSumFreeCount_eq_small_add_large (n : ℕ) :
    maximalSumFreeCount n =
      (smallMaximalSumFreeSets n).card + (largeMaximalSumFreeSets n).card := by
  rw [← Finset.card_union_of_disjoint (disjoint_small_large n),
    small_union_large]
  rfl

theorem smallMaximalSumFreeSets_subset_subsetsUpTo (n : ℕ) :
    smallMaximalSumFreeSets n ⊆ subsetsUpTo (interval n) (n / 10) := by
  intro A hA
  have h := mem_smallMaximalSumFreeSets.mp hA
  rw [mem_subsetsUpTo]
  refine ⟨h.1.subset, ?_⟩
  omega

/-- The small maximal sets contribute at most `(7/5)^n`. -/
theorem smallMaximalSumFreeSets_card_le_seven_fifths_pow (n : ℕ) :
    ((smallMaximalSumFreeSets n).card : ℝ) ≤ (7 / 5 : ℝ) ^ n := by
  calc
    ((smallMaximalSumFreeSets n).card : ℝ) ≤
        ((subsetsUpTo (interval n) (n / 10)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (smallMaximalSumFreeSets_subset_subsetsUpTo n)
    _ = ((subsetsUpTo (interval n) ((interval n).card / 10)).card : ℝ) := by
      rw [interval_card]
    _ ≤ (7 / 5 : ℝ) ^ (interval n).card :=
      card_subsetsUpTo_div_ten_le_seven_fifths_pow (interval n)
    _ = (7 / 5 : ℝ) ^ n := by rw [interval_card]

/-- The direct lower-layer estimate already makes the small-set contribution
little-o of the Erdős benchmark. -/
theorem smallMaximalSumFreeSets_isLittleO :
    (fun n : ℕ ↦ ((smallMaximalSumFreeSets n).card : ℝ)) =o[atTop] benchmark := by
  apply isLittleO_benchmark_of_eventually_norm_le_pow
    (a := (7 / 5 : ℝ)) (by norm_num) seven_fifths_lt_sqrt_two
  exact Eventually.of_forall fun n ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact smallMaximalSumFreeSets_card_le_seven_fifths_pow n

/-- The numerical saving left by the deletion double count after paying the
explicit `2^(n/2+n/2^30)` core-enumeration cost. -/
theorem deletion_exponent_le (n : ℕ)
    (hn : 2 ^ 33 ≤ n) :
    n / 2 + n / 2 ^ 30 + (2 * n) / (deletionDenom + 1) -
        (21 * (n / (10 * (deletionDenom + 1))) - 5) ≤
      n / 2 - n / 2 ^ 26 := by
  norm_num [deletionDenom] at hn ⊢
  omega

/-- The exponent subtracted in the finite cancellation is indeed available. -/
theorem deletion_exponent_budget (n : ℕ)
    (hn : 2 ^ 33 ≤ n) :
    21 * (n / (10 * (deletionDenom + 1))) - 5 ≤
      n / 2 + n / 2 ^ 30 + (2 * n) / (deletionDenom + 1) := by
  norm_num [deletionDenom] at hn ⊢
  omega

/-- Once the all-sum-free enumeration estimate is available, the large
maximal family has a fixed exponential saving over `2^(n/2)`. -/
theorem largeMaximalSumFreeSets_card_le_pow (n : ℕ)
    (hn : 2 ^ 33 ≤ n)
    (hsf : sumFreeCount n ≤ 2 ^ (n / 2 + n / 2 ^ 30)) :
    (largeMaximalSumFreeSets n).card ≤ 2 ^ (n / 2 - n / 2 ^ 26) := by
  have hnDelete : 10 * (deletionDenom + 1) ≤ n := by
    norm_num [deletionDenom] at hn ⊢
    omega
  exact (large_card_le_pow_of_sumFreeCount_le n
    (n / 2 + n / 2 ^ 30) hnDelete hsf (deletion_exponent_budget n hn)).trans
      (pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2)
        (deletion_exponent_le n hn))

/-- A fixed real base which is still below `sqrt 2`, but comfortably absorbs
the rounding in the integer exponent used for the large family. -/
noncomputable def largeBase : ℝ :=
  Real.rpow 2 ((1 / 2 : ℝ) - 1 / 2 ^ 27)

theorem largeBase_nonneg : 0 ≤ largeBase := by
  exact Real.rpow_nonneg (by norm_num) _

theorem largeBase_lt_sqrt_two : largeBase < Real.sqrt 2 := by
  rw [largeBase, Real.sqrt_eq_rpow]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)

/-- The natural-number power obtained from the double count is bounded by a
power of the fixed real base. -/
theorem cast_pow_deletion_exponent_le_largeBase_pow (n : ℕ)
    (hn : 2 ^ 33 ≤ n) :
    (((2 : ℕ) ^ (n / 2 - n / 2 ^ 26) : ℕ) : ℝ) ≤ largeBase ^ n := by
  have hcross :
      2 ^ 27 * (n / 2 - n / 2 ^ 26) ≤ (2 ^ 26 - 1) * n := by
    norm_num at hn ⊢
    omega
  have hcrossReal :
      (2 ^ 27 : ℝ) * ((n / 2 - n / 2 ^ 26 : ℕ) : ℝ) ≤
        (2 ^ 26 - 1 : ℝ) * (n : ℝ) := by
    norm_num at hcross ⊢
    exact_mod_cast hcross
  have hexponent :
      ((n / 2 - n / 2 ^ 26 : ℕ) : ℝ) ≤
        ((1 / 2 : ℝ) - 1 / 2 ^ 27) * (n : ℝ) := by
    norm_num at hcrossReal ⊢
    nlinarith
  calc
    (((2 : ℕ) ^ (n / 2 - n / 2 ^ 26) : ℕ) : ℝ) =
        (2 : ℝ) ^ (n / 2 - n / 2 ^ 26) := by norm_cast
    _ = Real.rpow 2 ((n / 2 - n / 2 ^ 26 : ℕ) : ℝ) := by
      exact (Real.rpow_natCast 2 (n / 2 - n / 2 ^ 26)).symm
    _ ≤ Real.rpow 2 (((1 / 2 : ℝ) - 1 / 2 ^ 27) * (n : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
    _ = largeBase ^ n := by
      rw [largeBase]
      exact (Real.rpow_mul (x := (2 : ℝ)) (by norm_num)
        ((1 / 2 : ℝ) - 1 / 2 ^ 27) (n : ℝ)).trans
          (Real.rpow_natCast _ n)

/-- Eventual real-power bound for the large maximal family. -/
theorem eventually_norm_largeMaximalSumFreeSets_card_le_pow :
    ∀ᶠ n : ℕ in atTop,
      ‖((largeMaximalSumFreeSets n).card : ℝ)‖ ≤ largeBase ^ n := by
  filter_upwards [Enumeration.eventually_sumFreeCount_le_pow,
    eventually_ge_atTop (2 ^ 33)] with n hsf hn
  have hlarge := largeMaximalSumFreeSets_card_le_pow n hn hsf
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    ((largeMaximalSumFreeSets n).card : ℝ) ≤
        (((2 : ℕ) ^ (n / 2 - n / 2 ^ 26) : ℕ) : ℝ) := by
      exact_mod_cast hlarge
    _ ≤ largeBase ^ n := cast_pow_deletion_exponent_le_largeBase_pow n hn

/-- The large-set contribution is little-o of `2^(n/2)`. -/
theorem largeMaximalSumFreeSets_isLittleO :
    (fun n : ℕ ↦ ((largeMaximalSumFreeSets n).card : ℝ)) =o[atTop] benchmark :=
  isLittleO_benchmark_of_eventually_norm_le_pow largeBase_nonneg
    largeBase_lt_sqrt_two eventually_norm_largeMaximalSumFreeSets_card_le_pow

/-- The resolved asymptotic estimate for the number of maximal sum-free
subsets of `[1,n]`. -/
theorem maximalSumFreeCount_isLittleO :
    (fun n : ℕ ↦ (maximalSumFreeCount n : ℝ)) =o[atTop] benchmark := by
  have h := smallMaximalSumFreeSets_isLittleO.add
    largeMaximalSumFreeSets_isLittleO
  apply h.congr'
  · exact Eventually.of_forall fun n ↦ by
      change ((smallMaximalSumFreeSets n).card : ℝ) +
          ((largeMaximalSumFreeSets n).card : ℝ) =
        (maximalSumFreeCount n : ℝ)
      exact_mod_cast (maximalSumFreeCount_eq_small_add_large n).symm
  · exact EventuallyEq.rfl

end Erdos877
