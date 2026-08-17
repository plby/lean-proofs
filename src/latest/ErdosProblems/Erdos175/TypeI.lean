/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib
import ErdosProblems.Erdos175.VaughanFourSums
import ErdosProblems.Erdos175.ReciprocalExpSumBound
import ErdosProblems.Erdos175.ReciprocalExpSumRounding

/-!
# Dyadic bookkeeping for Type-I sums

This file contains the combinatorial part of a Type-I estimate.  The
oscillatory estimate on one dyadic block is deliberately exposed as a
hypothesis: the results here turn such block estimates into estimates for an
arbitrary initial interval, while keeping track of coefficient bounds and the
single loss `Nat.log 2 N + 1` from dyadic subdivision.
-/

namespace Erdos175.TypeI

open scoped BigOperators

/-- The half-open dyadic interval `[2^j, 2^(j+1))`. -/
def dyadicBlock (j : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ j) (2 ^ (j + 1))

@[simp] lemma mem_dyadicBlock {j m : ℕ} :
    m ∈ dyadicBlock j ↔ 2 ^ j ≤ m ∧ m < 2 ^ (j + 1) := by
  simp [dyadicBlock]

/-- A dyadic interval has exactly `2^j` elements. -/
lemma card_dyadicBlock (j : ℕ) : (dyadicBlock j).card = 2 ^ j := by
  rw [dyadicBlock, Nat.card_Ico, pow_succ]
  omega

/-- Different dyadic blocks are disjoint. -/
lemma disjoint_dyadicBlock {i j : ℕ} (hij : i ≠ j) :
    Disjoint (dyadicBlock i) (dyadicBlock j) := by
  rw [Finset.disjoint_left]
  intro m hmi hmj
  have hmi' := mem_dyadicBlock.mp hmi
  have hmj' := mem_dyadicBlock.mp hmj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hp : 2 ^ (i + 1) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have hp : 2 ^ (j + 1) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- The number of dyadic blocks needed to cover `{1, ..., N}`. -/
def dyadicCount (N : ℕ) : ℕ := Nat.log 2 N + 1

/-- The last endpoint supplied by `dyadicCount` lies strictly beyond `N`. -/
lemma lt_two_pow_dyadicCount (N : ℕ) : N < 2 ^ dyadicCount N := by
  simpa [dyadicCount] using Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N

/-- The part of a dyadic block that remains in `{1, ..., N}`. -/
def truncatedDyadicBlock (N j : ℕ) : Finset ℕ :=
  (dyadicBlock j).filter (fun m => m ≤ N)

@[simp] lemma mem_truncatedDyadicBlock {N j m : ℕ} :
    m ∈ truncatedDyadicBlock N j ↔
      2 ^ j ≤ m ∧ m < 2 ^ (j + 1) ∧ m ≤ N := by
  simp [truncatedDyadicBlock, and_assoc]

/-- Exact dyadic decomposition up to a power of two. -/
lemma sum_dyadicBlocks {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (J : ℕ) :
    (∑ m ∈ Finset.Ico 1 (2 ^ J), f m) =
      ∑ j ∈ Finset.range J, ∑ m ∈ dyadicBlock j, f m := by
  induction J with
  | zero => simp [dyadicBlock]
  | succ J ih =>
      rw [Finset.sum_range_succ, ← ih]
      simpa [dyadicBlock, Nat.succ_eq_add_one] using
        (Finset.sum_Ico_consecutive f
          (show 1 ≤ 2 ^ J by
            have : 0 < 2 ^ J := pow_pos (by norm_num) J
            omega)
          (show 2 ^ J ≤ 2 ^ (J + 1) by
            rw [pow_succ]
            omega)).symm

/-- Exact dyadic decomposition of an arbitrary initial interval.  Empty
tails of the final block are removed by `truncatedDyadicBlock`. -/
lemma sum_truncatedDyadicBlocks {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N : ℕ) :
    (∑ m ∈ Finset.Ico 1 (N + 1), f m) =
      ∑ j ∈ Finset.range (dyadicCount N),
        ∑ m ∈ truncatedDyadicBlock N j, f m := by
  let g : ℕ → M := fun m => if m ≤ N then f m else 0
  have hdecomp := sum_dyadicBlocks g (dyadicCount N)
  have hupper : N + 1 ≤ 2 ^ dyadicCount N := by
    exact lt_two_pow_dyadicCount N
  have hleft :
      (∑ m ∈ Finset.Ico 1 (2 ^ dyadicCount N), g m) =
        ∑ m ∈ Finset.Ico 1 (N + 1), f m := by
    rw [← Finset.sum_Ico_consecutive g (by omega : 1 ≤ N + 1) hupper]
    have hfirst : (∑ m ∈ Finset.Ico 1 (N + 1), g m) =
        ∑ m ∈ Finset.Ico 1 (N + 1), f m := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_Ico] at hm
      simp [g, Nat.le_of_lt_succ hm.2]
    have htail :
        (∑ m ∈ Finset.Ico (N + 1) (2 ^ dyadicCount N), g m) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      simp only [Finset.mem_Ico] at hm
      simp [g, show ¬m ≤ N by omega]
    rw [hfirst, htail, add_zero]
  rw [hleft] at hdecomp
  rw [hdecomp]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [truncatedDyadicBlock, g, Finset.sum_filter]

/-- A finite Type-I sum: coefficients `a m` multiply a family of inner
oscillatory sums `F m`. -/
def sum (K : Type*) [Semiring K] (a F : ℕ → K) (N : ℕ) : K :=
  ∑ m ∈ Finset.Ico 1 (N + 1), a m * F m

/-- The contribution from one (possibly truncated) dyadic block. -/
def blockSum (K : Type*) [Semiring K] (a F : ℕ → K) (N j : ℕ) : K :=
  ∑ m ∈ truncatedDyadicBlock N j, a m * F m

/-- A Type-I sum is the sum of its dyadic block contributions. -/
lemma sum_eq_sum_blockSum {K : Type*} [Semiring K]
    (a F : ℕ → K) (N : ℕ) :
    sum K a F N =
      ∑ j ∈ Finset.range (dyadicCount N), blockSum K a F N j := by
  exact sum_truncatedDyadicBlocks (fun m => a m * F m) N

/-- Truncation can only decrease the cardinality of a dyadic block. -/
lemma card_truncatedDyadicBlock_le (N j : ℕ) :
    (truncatedDyadicBlock N j).card ≤ 2 ^ j := by
  rw [← card_dyadicBlock j]
  exact Finset.card_filter_le _ _

section NormBounds

variable {K : Type*} [NormedRing K]

/-- The triangle inequality for one Type-I block, with multiplication made
explicit on the right. -/
lemma norm_blockSum_le_sum_norm_mul (a F : ℕ → K) (N j : ℕ) :
    ‖blockSum K a F N j‖ ≤
      ∑ m ∈ truncatedDyadicBlock N j, ‖a m‖ * ‖F m‖ := by
  unfold blockSum
  calc
    ‖∑ m ∈ truncatedDyadicBlock N j, a m * F m‖ ≤
        ∑ m ∈ truncatedDyadicBlock N j, ‖a m * F m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m ∈ truncatedDyadicBlock N j, ‖a m‖ * ‖F m‖ := by
      apply Finset.sum_le_sum
      intro m hm
      exact norm_mul_le (a m) (F m)

/-- A uniform coefficient bound factors out of the elementary Type-I
triangle inequality. -/
lemma norm_blockSum_le_coeff_mul_sum_norm
    (a F : ℕ → K) (N j : ℕ) (A : ℝ)
    (ha : ∀ m ∈ truncatedDyadicBlock N j, ‖a m‖ ≤ A) :
    ‖blockSum K a F N j‖ ≤
      A * ∑ m ∈ truncatedDyadicBlock N j, ‖F m‖ := by
  calc
    ‖blockSum K a F N j‖ ≤
        ∑ m ∈ truncatedDyadicBlock N j, ‖a m‖ * ‖F m‖ :=
      norm_blockSum_le_sum_norm_mul a F N j
    _ ≤ ∑ m ∈ truncatedDyadicBlock N j, A * ‖F m‖ := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_right (ha m hm) (norm_nonneg _)
    _ = A * ∑ m ∈ truncatedDyadicBlock N j, ‖F m‖ := by
      rw [Finset.mul_sum]

/-- The completely elementary block estimate obtained when both the
coefficient and the inner sum are bounded pointwise. -/
lemma norm_blockSum_le_card_mul
    (a F : ℕ → K) (N j : ℕ) (A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (ha : ∀ m ∈ truncatedDyadicBlock N j, ‖a m‖ ≤ A)
    (hF : ∀ m ∈ truncatedDyadicBlock N j, ‖F m‖ ≤ B) :
    ‖blockSum K a F N j‖ ≤
      ((truncatedDyadicBlock N j).card : ℝ) * (A * B) := by
  calc
    ‖blockSum K a F N j‖ ≤
        ∑ m ∈ truncatedDyadicBlock N j, ‖a m‖ * ‖F m‖ :=
      norm_blockSum_le_sum_norm_mul a F N j
    _ ≤ ∑ _m ∈ truncatedDyadicBlock N j, A * B := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul (ha m hm) (hF m hm) (norm_nonneg _) hA
    _ = ((truncatedDyadicBlock N j).card : ℝ) * (A * B) := by
      simp

/-- A coarser version in which the block cardinality is replaced by `2^j`. -/
lemma norm_blockSum_le_two_pow_mul
    (a F : ℕ → K) (N j : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ m ∈ truncatedDyadicBlock N j, ‖a m‖ ≤ A)
    (hF : ∀ m ∈ truncatedDyadicBlock N j, ‖F m‖ ≤ B) :
    ‖blockSum K a F N j‖ ≤ (2 ^ j : ℝ) * (A * B) := by
  refine (norm_blockSum_le_card_mul a F N j A B hA hB ha hF).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mod_cast card_truncatedDyadicBlock_le N j) (mul_nonneg hA hB)

/-- The abstract analytic input for Type-I bookkeeping.  It says that every
coefficient sequence bounded by `A` admits the stated estimate on each
truncated dyadic block.  In the Granville--Ramaré application, proving this
predicate is the oscillatory-sum part of the argument. -/
def HasBlockEstimate (F : ℕ → K) (N : ℕ) (A : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ j < dyadicCount N, ∀ a : ℕ → K,
    (∀ m ∈ truncatedDyadicBlock N j, ‖a m‖ ≤ A) →
      ‖blockSum K a F N j‖ ≤ B j

/-- Summing arbitrary (not necessarily uniform) estimates over the dyadic
blocks costs exactly the sum of the block bounds. -/
lemma norm_sum_le_sum_block_bounds
    (a F : ℕ → K) (N : ℕ) (B : ℕ → ℝ)
    (hblock : ∀ j < dyadicCount N, ‖blockSum K a F N j‖ ≤ B j) :
    ‖sum K a F N‖ ≤ ∑ j ∈ Finset.range (dyadicCount N), B j := by
  rw [sum_eq_sum_blockSum]
  calc
    ‖∑ j ∈ Finset.range (dyadicCount N), blockSum K a F N j‖ ≤
        ∑ j ∈ Finset.range (dyadicCount N), ‖blockSum K a F N j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (dyadicCount N), B j := by
      apply Finset.sum_le_sum
      intro j hj
      exact hblock j (Finset.mem_range.mp hj)

/-- Apply an abstract dyadic Type-I estimate to coefficients bounded on the
whole initial interval. -/
lemma norm_sum_le_of_hasBlockEstimate
    (a F : ℕ → K) (N : ℕ) (A : ℝ) (B : ℕ → ℝ)
    (hestimate : HasBlockEstimate F N A B)
    (ha : ∀ m, 1 ≤ m → m ≤ N → ‖a m‖ ≤ A) :
    ‖sum K a F N‖ ≤ ∑ j ∈ Finset.range (dyadicCount N), B j := by
  apply norm_sum_le_sum_block_bounds
  intro j hj
  apply hestimate j hj a
  intro m hm
  have hm' := mem_truncatedDyadicBlock.mp hm
  have hpow : 1 ≤ 2 ^ j := by
    have : 0 < 2 ^ j := pow_pos (by norm_num) j
    omega
  exact ha m (hpow.trans hm'.1) hm'.2.2

/-- Uniform block bounds lose precisely the number of dyadic blocks. -/
lemma norm_sum_le_dyadicCount_mul
    (a F : ℕ → K) (N : ℕ) (C : ℝ)
    (hblock : ∀ j < dyadicCount N, ‖blockSum K a F N j‖ ≤ C) :
    ‖sum K a F N‖ ≤ (dyadicCount N : ℝ) * C := by
  calc
    ‖sum K a F N‖ ≤
        ∑ _j ∈ Finset.range (dyadicCount N), C := by
      apply norm_sum_le_sum_block_bounds
      exact hblock
    _ = (dyadicCount N : ℝ) * C := by simp

/-- The standard Type-I conclusion: a block theorem uniform for coefficients
of norm at most `A` gives a global bound with one exact dyadic-count factor. -/
lemma norm_sum_le_dyadicCount_mul_of_hasBlockEstimate
    (a F : ℕ → K) (N : ℕ) (A C : ℝ)
    (hestimate : HasBlockEstimate F N A (fun _ => C))
    (ha : ∀ m, 1 ≤ m → m ≤ N → ‖a m‖ ≤ A) :
    ‖sum K a F N‖ ≤ (dyadicCount N : ℝ) * C := by
  apply norm_sum_le_dyadicCount_mul
  intro j hj
  apply hestimate j hj a
  intro m hm
  have hm' := mem_truncatedDyadicBlock.mp hm
  have hpow : 1 ≤ 2 ^ j := by
    have : 0 < 2 ^ j := pow_pos (by norm_num) j
    omega
  exact ha m (hpow.trans hm'.1) hm'.2.2

/-- If the dyadic-count factor is itself bounded by a real logarithmic
parameter `L`, subdivision raises a bound `C * L^q` by exactly one power of
`L`.  This is the log-exponent bookkeeping used after a uniform dyadic
Type-I estimate. -/
lemma norm_sum_le_log_pow_succ
    (a F : ℕ → K) (N q : ℕ) (C L : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hcount : (dyadicCount N : ℝ) ≤ L)
    (hblock : ∀ j < dyadicCount N,
      ‖blockSum K a F N j‖ ≤ C * L ^ q) :
    ‖sum K a F N‖ ≤ C * L ^ (q + 1) := by
  calc
    ‖sum K a F N‖ ≤ (dyadicCount N : ℝ) * (C * L ^ q) :=
      norm_sum_le_dyadicCount_mul a F N (C * L ^ q) hblock
    _ = C * (dyadicCount N : ℝ) * L ^ q := by ring
    _ ≤ C * L * L ^ q := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcount hC) (pow_nonneg hL q)
    _ = C * L ^ (q + 1) := by
      rw [pow_succ]
      ring

end NormBounds

section InnerIntervals

/-- An inner interval sum, kept separate so the Type-I layer can be applied
to reciprocal phases or to any later oscillatory kernel. -/
def innerIntervalSum (K : Type*) [AddCommMonoid K]
    (w : ℕ → ℕ → K) (lower upper : ℕ → ℕ) (m : ℕ) : K :=
  ∑ n ∈ Finset.Ico (lower m) (upper m), w m n

/-- A Type-I double sum is exactly `sum` with its inner interval packaged as
`innerIntervalSum`. -/
lemma doubleSum_eq_sum_innerIntervalSum
    (K : Type*) [Semiring K] (a : ℕ → K) (w : ℕ → ℕ → K)
    (lower upper : ℕ → ℕ) (N : ℕ) :
    (∑ m ∈ Finset.Ico 1 (N + 1),
        a m * ∑ n ∈ Finset.Ico (lower m) (upper m), w m n) =
      sum K a (innerIntervalSum K w lower upper) N := by
  rfl

/-- The uniform-block bookkeeping theorem specialized to an actual Type-I
double sum. -/
lemma norm_doubleSum_le_dyadicCount_mul
    {K : Type*} [NormedRing K]
    (a : ℕ → K) (w : ℕ → ℕ → K) (lower upper : ℕ → ℕ)
    (N : ℕ) (C : ℝ)
    (hblock : ∀ j < dyadicCount N,
      ‖blockSum K a (innerIntervalSum K w lower upper) N j‖ ≤ C) :
    ‖∑ m ∈ Finset.Ico 1 (N + 1),
        a m * ∑ n ∈ Finset.Ico (lower m) (upper m), w m n‖ ≤
      (dyadicCount N : ℝ) * C := by
  change ‖sum K a (innerIntervalSum K w lower upper) N‖ ≤ _
  exact norm_sum_le_dyadicCount_mul a _ N C hblock

end InnerIntervals

section PartialSummation

/-- Masking a sequence below `A` turns an ordinary prefix into a local
prefix on `(A,t]`. -/
lemma sum_range_intervalMask {K : Type*} [AddCommMonoid K]
    (z : ℕ → K) (A t : ℕ) :
    (∑ n ∈ Finset.range (t + 1), if A < n then z n else 0) =
      ∑ n ∈ Finset.Ioc A t, z n := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  · intro n hn
    rfl

/-- Local summation by parts on a half-open natural interval. -/
lemma sum_Ioc_by_parts_local
    (f : ℕ → ℝ) (z : ℕ → ℂ) {A B : ℕ} (hAB : A < B) :
    (∑ n ∈ Finset.Ioc A B, f n • z n) =
      f B • (∑ n ∈ Finset.Ioc A B, z n) -
        ∑ t ∈ Finset.Ioc A (B - 1),
          (f (t + 1) - f t) • (∑ n ∈ Finset.Ioc A t, z n) := by
  let g : ℕ → ℂ := fun n => if A < n then z n else 0
  have habel := Finset.sum_Ioc_by_parts f g hAB
  have hleft : (∑ n ∈ Finset.Ioc A B, f n • g n) =
      ∑ n ∈ Finset.Ioc A B, f n • z n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp [g, hn.1]
  have hprefix (t : ℕ) :
      (∑ n ∈ Finset.range (t + 1), g n) =
        ∑ n ∈ Finset.Ioc A t, z n := by
    exact sum_range_intervalMask z A t
  rw [hleft, hprefix B, hprefix A] at habel
  have hzero : (∑ n ∈ Finset.Ioc A A, z n) = 0 := by simp
  rw [hzero, smul_zero, sub_zero] at habel
  simpa only [hprefix] using habel

/-- Adjacent differences telescope on a local interval. -/
lemma sum_Ioc_adjacent_sub (f : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    (∑ t ∈ Finset.Ioc A B, (f (t + 1) - f t)) =
      f (B + 1) - f (A + 1) := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
      rw [Finset.sum_Ioc_succ_top hAB, ih]
      ring

/-- Norm form of local summation by parts. -/
lemma norm_sum_Ioc_smul_le
    (f : ℕ → ℝ) (z : ℕ → ℂ) {A B : ℕ} (P : ℝ)
    (hAB : A < B) (_hP : 0 ≤ P) (hfB : 0 ≤ f B)
    (hmono : ∀ t, A < t → t < B → 0 ≤ f (t + 1) - f t)
    (hprefix : ∀ t, A ≤ t → t ≤ B →
      ‖∑ n ∈ Finset.Ioc A t, z n‖ ≤ P) :
    ‖∑ n ∈ Finset.Ioc A B, f n • z n‖ ≤
      (f B + (f B - f (A + 1))) * P := by
  rw [sum_Ioc_by_parts_local f z hAB]
  calc
    ‖f B • (∑ n ∈ Finset.Ioc A B, z n) -
          ∑ t ∈ Finset.Ioc A (B - 1),
            (f (t + 1) - f t) • (∑ n ∈ Finset.Ioc A t, z n)‖ ≤
        ‖f B • (∑ n ∈ Finset.Ioc A B, z n)‖ +
          ‖∑ t ∈ Finset.Ioc A (B - 1),
            (f (t + 1) - f t) • (∑ n ∈ Finset.Ioc A t, z n)‖ :=
      norm_sub_le _ _
    _ ≤ f B * P +
        ∑ t ∈ Finset.Ioc A (B - 1), (f (t + 1) - f t) * P := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hfB]
        exact mul_le_mul_of_nonneg_left (hprefix B (by omega) le_rfl) hfB
      · calc
          ‖∑ t ∈ Finset.Ioc A (B - 1),
              (f (t + 1) - f t) • (∑ n ∈ Finset.Ioc A t, z n)‖ ≤
              ∑ t ∈ Finset.Ioc A (B - 1),
                ‖(f (t + 1) - f t) •
                  (∑ n ∈ Finset.Ioc A t, z n)‖ := norm_sum_le _ _
          _ ≤ ∑ t ∈ Finset.Ioc A (B - 1),
                (f (t + 1) - f t) * P := by
            apply Finset.sum_le_sum
            intro t ht
            have ht' := Finset.mem_Ioc.mp ht
            have hdiff : 0 ≤ f (t + 1) - f t := hmono t ht'.1 (by omega)
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiff]
            exact mul_le_mul_of_nonneg_left
              (hprefix t (by omega) (by omega)) hdiff
    _ = (f B + (f B - f (A + 1))) * P := by
      rw [← Finset.sum_mul]
      have hle : A ≤ B - 1 := by omega
      rw [sum_Ioc_adjacent_sub f hle]
      have hsub : B - 1 + 1 = B := by omega
      rw [hsub]
      ring

/-- Granville--Ramaré Lemma 9.2 in a form without a finite `max`: `P` is
any common bound for all partial reciprocal sums on `(A,t]`. -/
lemma norm_logWeightedSum_le
    (z : ℕ → ℂ) {A B : ℕ} (P : ℝ)
    (hA : 1 ≤ A) (hAB : A < B) (hP : 0 ≤ P)
    (hprefix : ∀ t, A ≤ t → t ≤ B →
      ‖∑ n ∈ Finset.Ioc A t, z n‖ ≤ P) :
    ‖∑ n ∈ Finset.Ioc A B, Real.log (n : ℝ) • z n‖ ≤
      Real.log (((B : ℝ) ^ 2) / (A : ℝ)) * P := by
  have hBlog : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have hmono : ∀ t, A < t → t < B →
      0 ≤ Real.log ((t + 1 : ℕ) : ℝ) - Real.log (t : ℝ) := by
    intro t htA htB
    apply sub_nonneg.mpr
    exact Real.strictMonoOn_log.monotoneOn
      (show (t : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        exact_mod_cast (show 0 < t by omega))
      (show ((t + 1 : ℕ) : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        exact_mod_cast (show 0 < t + 1 by omega))
      (by norm_cast; omega)
  have hbasic := norm_sum_Ioc_smul_le
    (fun n => Real.log (n : ℝ)) z P hAB hP hBlog hmono hprefix
  refine hbasic.trans ?_
  apply mul_le_mul_of_nonneg_right ?_ hP
  have hApos : (0 : ℝ) < A := by positivity
  have hA1pos : (0 : ℝ) < A + 1 := by positivity
  have hlogA : Real.log (A : ℝ) ≤ Real.log (A + 1 : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hApos hA1pos (by norm_cast; omega)
  have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  have hAne : (A : ℝ) ≠ 0 := by exact_mod_cast (show A ≠ 0 by omega)
  rw [Real.log_div (pow_ne_zero 2 hBne) hAne, Real.log_pow]
  norm_num
  linarith

/-- Dyadic grouping gives the elementary harmonic bound needed in the Type-I
outer sum.  Keeping the exact natural logarithm count avoids any analytic
integration argument. -/
lemma sum_inv_le_dyadicCount (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹) ≤ dyadicCount N := by
  have hsets : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hsets, sum_truncatedDyadicBlocks]
  calc
    (∑ j ∈ Finset.range (dyadicCount N),
        ∑ m ∈ truncatedDyadicBlock N j, (m : ℝ)⁻¹) ≤
        ∑ _j ∈ Finset.range (dyadicCount N), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        (∑ m ∈ truncatedDyadicBlock N j, (m : ℝ)⁻¹) ≤
            ∑ _m ∈ truncatedDyadicBlock N j, ((2 ^ j : ℕ) : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro m hm
          have hm' := mem_truncatedDyadicBlock.mp hm
          rw [← one_div, ← one_div]
          exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hm'.1)
        _ = ((truncatedDyadicBlock N j).card : ℝ) *
            ((2 ^ j : ℕ) : ℝ)⁻¹ := by simp
        _ ≤ ((2 ^ j : ℕ) : ℝ) * ((2 ^ j : ℕ) : ℝ)⁻¹ := by
          gcongr
          exact_mod_cast card_truncatedDyadicBlock_le N j
        _ = 1 := by
          rw [mul_inv_cancel₀]
          positivity
    _ = dyadicCount N := by simp

/-- Convert the exact block count to a real logarithmic factor. -/
lemma dyadicCount_cast_le_log_div_add_one {N : ℕ} (hN : N ≠ 0) :
    (dyadicCount N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 + 1 := by
  have hpowN : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN
  have hpowpos : (0 : ℝ) < ((2 ^ Nat.log 2 N : ℕ) : ℝ) := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hN
  have hpowNR : (((2 ^ Nat.log 2 N : ℕ) : ℝ)) ≤ (N : ℝ) := by
    exact_mod_cast hpowN
  have hlog := Real.strictMonoOn_log.monotoneOn hpowpos hNpos hpowNR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    rw [show (((2 ^ Nat.log 2 N : ℕ) : ℝ)) =
      (2 : ℝ) ^ Nat.log 2 N by norm_num] at hlog
    rw [Real.log_pow] at hlog
    simpa [mul_comm] using hlog
  simpa [dyadicCount] using add_le_add_right hk 1

/-! ## Endpoint scaling for Proposition 8.1 -/

/-- The hypotheses used in Section 9 remain valid after replacing the phase
parameter `x` by `x/m` and the interval endpoints by `y/m,y'/m`. -/
lemma scaled_endpoint_conditions
    {x y y' : ℝ} {m M : ℕ}
    (hx : 0 < x) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hyM : 1000 * (M : ℝ) ≤ y)
    (hyy' : y ≤ y') (hy' : y' ≤ 2 * y)
    (hscale : y ≤ 4 * x ^ (3 / 5 : ℝ)) :
    0 < x / (m : ℝ) ∧
      1000 ≤ y / (m : ℝ) ∧
      y / (m : ℝ) ≤ y' / (m : ℝ) ∧
      y' / (m : ℝ) ≤ 2 * (y / (m : ℝ)) ∧
      y / (m : ℝ) ≤ 4 * (x / (m : ℝ)) ^ (3 / 5 : ℝ) := by
  have hmpos : (0 : ℝ) < m := by positivity
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmMR : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have h1000m : (1000 : ℝ) * m ≤ y :=
    (mul_le_mul_of_nonneg_left hmMR (by norm_num)).trans hyM
  have hmRpow : (m : ℝ) ^ (3 / 5 : ℝ) ≤ (m : ℝ) :=
    Real.rpow_le_self_of_one_le hmone (by norm_num)
  have hxpow : 0 ≤ x ^ (3 / 5 : ℝ) := Real.rpow_nonneg hx.le _
  have hdivpow : x ^ (3 / 5 : ℝ) / (m : ℝ) ≤
      x ^ (3 / 5 : ℝ) / (m : ℝ) ^ (3 / 5 : ℝ) :=
    div_le_div_of_nonneg_left hxpow (by positivity) hmRpow
  refine ⟨div_pos hx hmpos, (le_div_iff₀ hmpos).2 h1000m,
    (div_le_div_iff_of_pos_right hmpos).2 hyy', ?_, ?_⟩
  · rw [show 2 * (y / (m : ℝ)) = (2 * y) / (m : ℝ) by ring]
    exact (div_le_div_iff_of_pos_right hmpos).2 hy'
  · calc
      y / (m : ℝ) ≤ (4 * x ^ (3 / 5 : ℝ)) / (m : ℝ) :=
        (div_le_div_iff_of_pos_right hmpos).2 hscale
      _ = 4 * (x ^ (3 / 5 : ℝ) / (m : ℝ)) := by ring
      _ ≤ 4 * (x ^ (3 / 5 : ℝ) / (m : ℝ) ^ (3 / 5 : ℝ)) := by
        gcongr
      _ = 4 * (x / (m : ℝ)) ^ (3 / 5 : ℝ) := by
        rw [Real.div_rpow hx.le hmpos.le]

/-- Dividing an interval with `y' ≤ 2y` by a positive natural number
produces a dyadic interval up to the single unavoidable rounding unit. -/
lemma quotient_interval_sub_le {y y' m : ℕ} (hm : 1 ≤ m)
    (hy' : y' ≤ 2 * y) :
    y' / m - y / m ≤ y / m + 1 := by
  have hB : y' / m ≤ 2 * (y / m) + 1 := by
    calc
      y' / m ≤ (2 * y) / m := Nat.div_le_div_right hy'
      _ = (y + y) / m := by rw [two_mul]
      _ ≤ y / m + y / m + 1 :=
        Nat.add_div_le_div_add_div_add_one y y m
      _ = 2 * (y / m) + 1 := by omega
  omega

/-- A single global fourth-derivative inequality at `M` implies the
rescaled inequality needed for every outer variable `m ≤ M`.  The `+1`
is exactly the natural-floor endpoint in the reciprocal-sum theorem. -/
lemma scaled_fourth_derivative_condition
    {x : ℝ} {y m M : ℕ} (hx : 0 ≤ x) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hglobal : 12 * x * (M : ℝ) ^ 3 ≤ (y : ℝ) ^ 4) :
    12 * (x / (m : ℝ)) ≤ (((y / m) + 1 : ℕ) : ℝ) ^ 4 := by
  have hmpos : (0 : ℝ) < m := by positivity
  have hmpow : (m : ℝ) ^ 3 ≤ (M : ℝ) ^ 3 := by
    gcongr
  have hnum : 12 * x * (m : ℝ) ^ 3 ≤ (y : ℝ) ^ 4 :=
    (mul_le_mul_of_nonneg_left hmpow (mul_nonneg (by norm_num) hx)).trans hglobal
  have hlocal :
      12 * (x / (m : ℝ)) ≤ ((y : ℝ) / (m : ℝ)) ^ 4 := by
    calc
      12 * (x / (m : ℝ)) =
          (12 * x * (m : ℝ) ^ 3) / (m : ℝ) ^ 4 := by field_simp
      _ ≤ (y : ℝ) ^ 4 / (m : ℝ) ^ 4 :=
        (div_le_div_iff_of_pos_right (pow_pos hmpos 4)).2 hnum
      _ = ((y : ℝ) / (m : ℝ)) ^ 4 := by rw [div_pow]
  have hfloor :
      ((y : ℝ) / (m : ℝ)) < (((y / m) + 1 : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one ((y : ℝ) / (m : ℝ))
    rw [Nat.floor_div_natCast] at h
    simpa using h
  exact hlocal.trans (by gcongr)

/-- Rescaling the reciprocal phase from `x` to `x/m`. -/
lemma div_div_natCast_eq_div_mul_natCast
    (x : ℝ) {m l : ℕ} (hm : m ≠ 0) (hl : l ≠ 0) :
    (x / (m : ℝ)) / (l : ℝ) = x / ((m * l : ℕ) : ℝ) := by
  push_cast
  field_simp

/-- Exact identification of a product-phase sum on an arbitrary natural
interval with a reciprocal exponential sum after rescaling by the outer
variable. -/
lemma vaughanProductInner_eq_reciprocalExpSum
    (x : ℝ) (A B m : ℕ) (hm : 1 ≤ m) :
    (∑ l ∈ Finset.Ioc A B,
        Vaughan.reciprocalPhase x (m * l)) =
      reciprocalExpSum (x / (m : ℝ)) A B := by
  have hm0 : m ≠ 0 := by omega
  unfold reciprocalExpSum
  apply Finset.sum_congr rfl
  intro l hl
  have hl0 : l ≠ 0 := by
    have hl' := Finset.mem_Ioc.mp hl
    exact Nat.ne_of_gt ((Nat.zero_le _).trans_lt hl'.1)
  unfold Vaughan.reciprocalPhase e
  rw [div_div_natCast_eq_div_mul_natCast x hm0 hl0]

/-- Quotient-endpoint specialization of
`vaughanProductInner_eq_reciprocalExpSum`. -/
lemma vaughanInner_eq_reciprocalExpSum
    (x : ℝ) (y y' m : ℕ) (hm : 1 ≤ m) :
    (∑ l ∈ Finset.Ioc (y / m) (y' / m),
        Vaughan.reciprocalPhase x (m * l)) =
      reciprocalExpSum (x / (m : ℝ)) (y / m) (y' / m) :=
  vaughanProductInner_eq_reciprocalExpSum x (y / m) (y' / m) m hm

/-- The short-prefix complement to the q-free high-frequency estimate.
When the first-derivative test does not apply and the optimal Weyl shift
hits its length cap, taking `q = ⌊√N⌋` in the proved fourth-power
estimate gives an `N^(3/8) C^(1/2)` remainder after taking fourth roots.
The nested square roots keep the statement and proof free of fractional
power normalization side conditions. -/
lemma norm_reciprocalExpRange_le_cappedShift
    (x : ℝ) (C N : ℕ) (hx : 0 < x) (hC : 0 < C)
    (hN : 0 < N) (hNC : N ≤ C)
    (hone : 12 * x ≤ (C : ℝ) ^ 4)
    (hnotHalf : ¬ x / (C : ℝ) ^ 2 ≤ 1 / 2)
    (hnotHigh : ¬ (C : ℝ) ^ 4 <
      12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    ‖reciprocalExpRange x C N‖ ≤
      16 * Real.sqrt (Real.sqrt (
        (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) *
          (1 + Real.log C) ^ 2)) := by
  let q := Nat.sqrt N
  have hq : 1 ≤ q := by
    dsimp [q]
    exact Nat.sqrt_pos.mpr hN
  have hqN : q ^ 2 ≤ N := by
    dsimp [q]
    exact Nat.sqrt_le' N
  have hsqrtCap : N ≤ 4 * q ^ 2 := by
    have hs := Nat.lt_succ_sqrt' N
    have hqpos : 0 < q := by omega
    dsimp [q] at hs ⊢
    nlinarith
  have hderiv : 12 * x * (q : ℝ) ^ 3 ≤ (C : ℝ) ^ 4 := by
    exact le_of_not_gt hnotHigh
  have hfour := reciprocalExpRange_fourth_le x C N q hx hC hq hqN hderiv
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hNCr : (N : ℝ) ≤ C := by exact_mod_cast hNC
  have hcapR : (N : ℝ) ≤ 4 * (q : ℝ) ^ 2 := by exact_mod_cast hsqrtCap
  have hCadd : ((C + N : ℕ) : ℝ) ≤ 2 * (C : ℝ) := by
    push_cast
    linarith
  have hxlower : (C : ℝ) ^ 2 < 2 * x := by
    have := lt_of_not_ge hnotHalf
    rw [lt_div_iff₀ (by positivity)] at this
    norm_num at this ⊢
    nlinarith
  have hratio :
      (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) ≤ 6 * (C : ℝ) ^ 2 := by
    have hp : ((C + N : ℕ) : ℝ) ^ 4 ≤ (2 * (C : ℝ)) ^ 4 := by gcongr
    rw [div_le_iff₀ (by positivity)]
    calc
      ((C + N : ℕ) : ℝ) ^ 4 ≤ (2 * (C : ℝ)) ^ 4 := hp
      _ ≤ (6 * (C : ℝ) ^ 2) * (6 * x) := by
        nlinarith [sq_nonneg ((C : ℝ) ^ 2)]
  have hqRatio :
      (N : ℝ) ^ 3 / (q : ℝ) ^ 3 ≤
        8 * Real.sqrt ((N : ℝ) ^ 3) := by
    have hcube : (N : ℝ) ^ 3 ≤ 64 * (q : ℝ) ^ 6 := by
      have hcubed : (N : ℝ) ^ 3 ≤ (4 * (q : ℝ) ^ 2) ^ 3 := by gcongr
      nlinarith
    have hsqrtBound : Real.sqrt ((N : ℝ) ^ 3) ≤ 8 * (q : ℝ) ^ 3 := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · nlinarith
    have hsqrtSq : Real.sqrt ((N : ℝ) ^ 3) ^ 2 = (N : ℝ) ^ 3 :=
      Real.sq_sqrt (by positivity)
    rw [div_le_iff₀ (by positivity)]
    have hmul := mul_le_mul_of_nonneg_left hsqrtBound
      (Real.sqrt_nonneg ((N : ℝ) ^ 3))
    nlinarith
  have hlogC : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ C by omega))
  have hlogFactor : 1 ≤ (1 + Real.log (C : ℝ)) ^ 2 := by nlinarith
  have hharm :
      finiteHarmonic (q ^ 2) * finiteHarmonic q ≤
        2 * (1 + Real.log (C : ℝ)) ^ 2 := by
    have hqC : q ≤ C := (Nat.sqrt_le_self N).trans hNC
    have hlogq : Real.log (q : ℝ) ≤ Real.log (C : ℝ) :=
      Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqC)
    calc
      finiteHarmonic (q ^ 2) * finiteHarmonic q ≤
          2 * (1 + Real.log (q : ℝ)) ^ 2 := finiteHarmonic_sq_mul_le hq
      _ ≤ 2 * (1 + Real.log (C : ℝ)) ^ 2 := by gcongr
  let X := (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) *
    (1 + Real.log C) ^ 2
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hsqrtN : (N : ℝ) ≤ Real.sqrt ((N : ℝ) ^ 3) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast hN]
  have hNcube : (N : ℝ) ^ 3 ≤ X := by
    dsimp [X]
    calc
      (N : ℝ) ^ 3 = (N : ℝ) ^ 2 * (N : ℝ) := by ring
      _ ≤ (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) := by gcongr
      _ ≤ (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) *
          (1 + Real.log C) ^ 2 := by
        exact le_mul_of_one_le_right (by positivity) hlogFactor
  have hdiag :
      512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 ≤ 2048 * X := by
    have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hq2]
    calc
      512 * (N : ℝ) ^ 4 =
          (512 * (N : ℝ) ^ 3) * (N : ℝ) := by ring
      _ ≤ (512 * (N : ℝ) ^ 3) * (4 * (q : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hcapR (by positivity)
      _ = 2048 * (N : ℝ) ^ 3 * (q : ℝ) ^ 2 := by ring
      _ ≤ 2048 * X * (q : ℝ) ^ 2 := by gcongr
      _ = (2048 * X) * (q : ℝ) ^ 2 := by ring
  have hterminal :
      (512 : ℝ) * (N : ℝ) ^ 3 *
          (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) ≤
        49152 * X := by
    calc
      (512 : ℝ) * (N : ℝ) ^ 3 *
            (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
            (finiteHarmonic (q ^ 2) * finiteHarmonic q) =
          512 * ((N : ℝ) ^ 3 / (q : ℝ) ^ 3) *
            (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) *
              (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by ring
      _ ≤ 512 * (8 * Real.sqrt ((N : ℝ) ^ 3)) *
            (6 * (C : ℝ) ^ 2) *
              (2 * (1 + Real.log C) ^ 2) := by
        gcongr
        exact mul_nonneg (finiteHarmonic_nonneg _) (finiteHarmonic_nonneg _)
      _ = 49152 * X := by dsimp [X]; ring
  have hpow : ‖reciprocalExpRange x C N‖ ^ 4 ≤ (16 * Real.sqrt (Real.sqrt X)) ^ 4 := by
    have hsqrtX : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX
    have hsqrtsqrt : Real.sqrt (Real.sqrt X) ^ 2 = Real.sqrt X :=
      Real.sq_sqrt (Real.sqrt_nonneg X)
    have hnested : Real.sqrt (Real.sqrt X) ^ 4 = X := by
      calc
        Real.sqrt (Real.sqrt X) ^ 4 =
            (Real.sqrt (Real.sqrt X) ^ 2) ^ 2 := by ring
        _ = Real.sqrt X ^ 2 := by rw [hsqrtsqrt]
        _ = X := hsqrtX
    calc
      ‖reciprocalExpRange x C N‖ ^ 4 ≤
          512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
            (512 : ℝ) * (N : ℝ) ^ 3 *
              (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
              (finiteHarmonic (q ^ 2) * finiteHarmonic q) := hfour
      _ ≤ 2048 * X + 49152 * X := add_le_add hdiag hterminal
      _ ≤ 65536 * X := by nlinarith
      _ = (16 * Real.sqrt (Real.sqrt X)) ^ 4 := by
        rw [mul_pow, hnested]
        norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
    (by positivity) hpow

/-- An unconditional (within the standard dyadic derivative range) concrete
bound for a reciprocal exponential sum.  The three displayed terms are,
respectively, the first-derivative branch, the optimized two-step branch,
and the capped-shift remainder.  The proof chooses the applicable branch by
decidable real inequalities, so no exponential-sum estimate remains as a
hypothesis. -/
lemma norm_reciprocalExpRange_le_threeBranch
    (x : ℝ) (C N : ℕ) (hx : 0 < x) (hC : 0 < C)
    (hN : 0 < N) (hNC : N ≤ C)
    (hone : 12 * x ≤ (C : ℝ) ^ 4) :
    ‖reciprocalExpRange x C N‖ ≤
      ((C + N : ℕ) : ℝ) ^ 2 / x +
      128 * (N : ℝ) * (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log C) +
      16 * Real.sqrt (Real.sqrt (
        (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) *
          (1 + Real.log C) ^ 2)) := by
  have hfirst_nonneg : 0 ≤ ((C + N : ℕ) : ℝ) ^ 2 / x := by positivity
  have hhigh_nonneg : 0 ≤
      128 * (N : ℝ) * (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log C) := by positivity
  have hcap_nonneg : 0 ≤
      16 * Real.sqrt (Real.sqrt (
        (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) *
          (1 + Real.log C) ^ 2)) := by positivity
  by_cases hhalf : x / (C : ℝ) ^ 2 ≤ 1 / 2
  · have h := norm_reciprocalExpRange_le_firstDerivative x C N hx hC hhalf
    linarith
  · by_cases hhigh : (C : ℝ) ^ 4 <
        12 * x * (Nat.sqrt N : ℝ) ^ 3
    · have h := norm_reciprocalExpRange_le_dyadic_qfree
        x C N hx hC hN hNC hone hhigh
      linarith
    · have h := norm_reciprocalExpRange_le_cappedShift
        x C N hx hC hN hNC hone hhalf hhigh
      linarith

/-- Natural interval form of `norm_reciprocalExpRange_le_threeBranch`. -/
lemma norm_reciprocalExpSum_le_threeBranch
    (x : ℝ) (A B : ℕ) (hx : 0 < x) (hAB : A < B)
    (hdyadic : B - A ≤ A + 1)
    (hone : 12 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 4) :
    ‖reciprocalExpSum x A B‖ ≤
      ((B + 1 : ℕ) : ℝ) ^ 2 / x +
      128 * ((B - A : ℕ) : ℝ) *
        (x / ((A + 1 : ℕ) : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt (1 + Real.log (((A + 1 : ℕ) : ℝ))) +
      16 * Real.sqrt (Real.sqrt (
        ((A + 1 : ℕ) : ℝ) ^ 2 *
          Real.sqrt (((B - A : ℕ) : ℝ) ^ 3) *
            (1 + Real.log (((A + 1 : ℕ) : ℝ))) ^ 2)) := by
  rw [reciprocalExpSum_eq_range x A B hAB.le]
  have h := norm_reciprocalExpRange_le_threeBranch x (A + 1) (B - A)
    hx (by omega) (by omega) hdyadic
    (by simpa using hone)
  have hend : A + 1 + (B - A) = B + 1 := by omega
  simpa only [hend] using h

/-- The explicit three-branch majorant, packaged for partial summation. -/
noncomputable def threeBranchBound (x : ℝ) (A B : ℕ) : ℝ :=
  ((B + 1 : ℕ) : ℝ) ^ 2 / x +
    128 * ((B - A : ℕ) : ℝ) *
      (x / ((A + 1 : ℕ) : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log (((A + 1 : ℕ) : ℝ))) +
    16 * Real.sqrt (Real.sqrt (
      ((A + 1 : ℕ) : ℝ) ^ 2 *
        Real.sqrt (((B - A : ℕ) : ℝ) ^ 3) *
          (1 + Real.log (((A + 1 : ℕ) : ℝ))) ^ 2))

/-- A closed-form numerator for summing the three-branch bounds over
`1 ≤ m ≤ M`.  Its three summands correspond to the three summands in
`threeBranchBound`; division by `m` is proved below. -/
noncomputable def threeBranchOuterNumerator (x : ℝ) (y M : ℕ) : ℝ :=
  16 * (y : ℝ) ^ 2 / x +
    256 * (y : ℝ) *
      (x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log (2 * y : ℕ)) +
    16 * Real.sqrt (Real.sqrt (
      (2 * (y : ℝ)) ^ 3 * Real.sqrt (2 * (y : ℝ)) * (M : ℝ) *
        (1 + Real.log (2 * y : ℕ)) ^ 2))

lemma threeBranchBound_nonneg {x : ℝ} (A B : ℕ) (hx : 0 < x) :
    0 ≤ threeBranchBound x A B := by
  unfold threeBranchBound
  positivity

/-- Each concrete inner bound has harmonic dependence on the outer
variable after replacing its parameters by the global endpoints. -/
lemma threeBranchBound_le_outerNumerator_div
    {x : ℝ} {y y' m M : ℕ} (hx : 0 < x) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hA : 1 ≤ y / m) (hy' : y' ≤ 2 * y) :
    threeBranchBound (x / (m : ℝ)) (y / m) (y' / m) ≤
      threeBranchOuterNumerator x y M / (m : ℝ) := by
  let A := y / m
  let B := y' / m
  let C := A + 1
  let N := B - A
  let a : ℝ := 2 * (y : ℝ)
  let L : ℝ := 1 + Real.log a
  have hmpos : (0 : ℝ) < m := by positivity
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmMR : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hmy : m ≤ y := by
    have h := (Nat.le_div_iff_mul_le (show 0 < m by omega)).mp hA
    simpa using h
  have hypos : (0 : ℝ) < y := by
    exact_mod_cast (lt_of_lt_of_le (show 0 < m by omega) hmy)
  have hapos : 0 < a := by dsimp [a]; positivity
  have hAcast : (A : ℝ) ≤ (y : ℝ) / (m : ℝ) := by
    dsimp [A]
    exact Nat.cast_div_le
  have hAone : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hCpos : (0 : ℝ) < C := by positivity
  have hCreal : (C : ℝ) ≤ a / (m : ℝ) := by
    have hCA : C ≤ 2 * A := by
      dsimp [C]
      omega
    calc
      (C : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hCA
      _ ≤ 2 * ((y : ℝ) / (m : ℝ)) := by gcongr
      _ = a / (m : ℝ) := by dsimp [a]; ring
  have hCa : (C : ℝ) ≤ a := hCreal.trans (div_le_self hapos.le hmone)
  have hNnat : N ≤ C := by
    dsimp [N, C, A, B]
    exact quotient_interval_sub_le hm hy'
  have hNC : (N : ℝ) ≤ C := by exact_mod_cast hNnat
  have hBC : B + 1 ≤ 2 * C := by
    have hB : B ≤ 2 * A + 1 := by
      dsimp [A, B]
      have hs := quotient_interval_sub_le hm hy'
      omega
    dsimp [C]
    omega
  have hBCreal : ((B + 1 : ℕ) : ℝ) ≤ 2 * (C : ℝ) := by exact_mod_cast hBC
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    have : 0 ≤ Real.log a := Real.log_nonneg (by
      dsimp [a]
      exact_mod_cast (show 1 ≤ 2 * y by omega))
    linarith
  have hlog : 1 + Real.log (C : ℝ) ≤ L := by
    dsimp [L]
    gcongr
  have hfirst :
      ((B + 1 : ℕ) : ℝ) ^ 2 / (x / (m : ℝ)) ≤
        (16 * (y : ℝ) ^ 2 / x) / (m : ℝ) := by
    have hupper : ((B + 1 : ℕ) : ℝ) ≤
        4 * (y : ℝ) / (m : ℝ) := by
      calc
        ((B + 1 : ℕ) : ℝ) ≤ 2 * (C : ℝ) := hBCreal
        _ ≤ 2 * (a / (m : ℝ)) := by gcongr
        _ = 4 * (y : ℝ) / (m : ℝ) := by dsimp [a]; ring
    have hid :
        (16 * (y : ℝ) ^ 2 / x) / (m : ℝ) =
          (4 * (y : ℝ) / (m : ℝ)) ^ 2 / (x / (m : ℝ)) := by
      field_simp
      norm_num
    rw [hid]
    exact div_le_div_of_nonneg_right (by gcongr) (by positivity)
  have hfloor : (y : ℝ) / (m : ℝ) ≤ (C : ℝ) := by
    have h := Nat.lt_floor_add_one ((y : ℝ) / (m : ℝ))
    rw [Nat.floor_div_natCast] at h
    simpa [C, A] using h.le
  have hbase :
      (x / (m : ℝ)) / (C : ℝ) ^ 4 ≤
        x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4 := by
    calc
      (x / (m : ℝ)) / (C : ℝ) ^ 4 ≤
          (x / (m : ℝ)) / ((y : ℝ) / (m : ℝ)) ^ 4 := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
      _ = x * (m : ℝ) ^ 3 / (y : ℝ) ^ 4 := by field_simp
      _ ≤ x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4 := by gcongr
  have hsixth :
      128 * (N : ℝ) *
          ((x / (m : ℝ)) / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
            Real.sqrt (1 + Real.log C) ≤
        (256 * (y : ℝ) *
          (x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
            Real.sqrt L) / (m : ℝ) := by
    have hNupper : (N : ℝ) ≤ 2 * (y : ℝ) / (m : ℝ) := hNC.trans hCreal
    have hid :
        (256 * (y : ℝ) *
          (x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
            Real.sqrt L) / (m : ℝ) =
          128 * (2 * (y : ℝ) / (m : ℝ)) *
            (x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
              Real.sqrt L := by ring
    rw [hid]
    gcongr
  let X : ℝ := (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) *
    (1 + Real.log C) ^ 2
  let XG : ℝ := a ^ 3 * Real.sqrt a * (M : ℝ) * L ^ 2
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hXG : 0 ≤ XG := by dsimp [XG]; positivity
  have hsqrtN : Real.sqrt ((N : ℝ) ^ 3) ≤
      (C : ℝ) * Real.sqrt a := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hpow : (N : ℝ) ^ 3 ≤ (C : ℝ) ^ 3 := by gcongr
      have hCa' : (C : ℝ) ^ 3 ≤ (C : ℝ) ^ 2 * a := by
        nlinarith [sq_nonneg (C : ℝ)]
      calc
        (N : ℝ) ^ 3 ≤ (C : ℝ) ^ 3 := hpow
        _ ≤ (C : ℝ) ^ 2 * a := hCa'
        _ = ((C : ℝ) * Real.sqrt a) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hapos.le]
  have hXscale : X ≤ XG / (m : ℝ) ^ 4 := by
    have hcore : X ≤
        (a / (m : ℝ)) ^ 3 * Real.sqrt a * L ^ 2 := by
      dsimp [X]
      calc
        (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) *
            (1 + Real.log C) ^ 2 ≤
          (C : ℝ) ^ 2 * ((C : ℝ) * Real.sqrt a) * L ^ 2 := by gcongr
        _ = (C : ℝ) ^ 3 * Real.sqrt a * L ^ 2 := by ring
        _ ≤ (a / (m : ℝ)) ^ 3 * Real.sqrt a * L ^ 2 := by gcongr
    calc
      X ≤ (a / (m : ℝ)) ^ 3 * Real.sqrt a * L ^ 2 := hcore
      _ = (a ^ 3 * Real.sqrt a * (m : ℝ) * L ^ 2) /
          (m : ℝ) ^ 4 := by field_simp
      _ ≤ (a ^ 3 * Real.sqrt a * (M : ℝ) * L ^ 2) /
          (m : ℝ) ^ 4 := by gcongr
      _ = XG / (m : ℝ) ^ 4 := by rfl
  have hcaproot : Real.sqrt (Real.sqrt X) ≤
      Real.sqrt (Real.sqrt XG) / (m : ℝ) := by
    have hu4 : Real.sqrt (Real.sqrt X) ^ 4 = X := by
      calc
        Real.sqrt (Real.sqrt X) ^ 4 =
            (Real.sqrt (Real.sqrt X) ^ 2) ^ 2 := by ring
        _ = Real.sqrt X ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg X)]
        _ = X := Real.sq_sqrt hX
    have hv4 : (Real.sqrt (Real.sqrt XG) / (m : ℝ)) ^ 4 =
        XG / (m : ℝ) ^ 4 := by
      rw [div_pow]
      congr 1
      calc
        Real.sqrt (Real.sqrt XG) ^ 4 =
            (Real.sqrt (Real.sqrt XG) ^ 2) ^ 2 := by ring
        _ = Real.sqrt XG ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg XG)]
        _ = XG := Real.sq_sqrt hXG
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity)
    rw [hu4, hv4]
    exact hXscale
  have hcap : 16 * Real.sqrt (Real.sqrt X) ≤
      (16 * Real.sqrt (Real.sqrt XG)) / (m : ℝ) := by
    rw [show (16 * Real.sqrt (Real.sqrt XG)) / (m : ℝ) =
      16 * (Real.sqrt (Real.sqrt XG) / (m : ℝ)) by ring]
    gcongr
  change
    ((B + 1 : ℕ) : ℝ) ^ 2 / (x / (m : ℝ)) +
        128 * (N : ℝ) *
          ((x / (m : ℝ)) / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
            Real.sqrt (1 + Real.log C) +
        16 * Real.sqrt (Real.sqrt X) ≤ _
  unfold threeBranchOuterNumerator
  have ha_cast : (((2 * y : ℕ) : ℝ)) = a := by
    dsimp [a]
    push_cast
    rfl
  rw [ha_cast]
  change _ ≤
    ((16 * (y : ℝ) ^ 2 / x) +
      (256 * (y : ℝ) *
        (x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4) ^ (1 / 6 : ℝ) * Real.sqrt L) +
      16 * Real.sqrt (Real.sqrt XG)) / (m : ℝ)
  calc
    _ ≤ (16 * (y : ℝ) ^ 2 / x) / (m : ℝ) +
          (256 * (y : ℝ) *
            (x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
              Real.sqrt L) / (m : ℝ) +
          (16 * Real.sqrt (Real.sqrt XG)) / (m : ℝ) := by
      exact add_le_add (add_le_add hfirst hsixth) hcap
    _ = _ := by ring

lemma threeBranchOuterNumerator_nonneg {x : ℝ} (y M : ℕ) (hx : 0 < x) :
    0 ≤ threeBranchOuterNumerator x y M := by
  unfold threeBranchOuterNumerator
  positivity

/-- Increasing the upper endpoint can only increase the packaged majorant. -/
lemma threeBranchBound_mono_upper {x : ℝ} {A B B' : ℕ}
    (hx : 0 < x) (hAB : A ≤ B) (hBB' : B ≤ B') :
    threeBranchBound x A B ≤ threeBranchBound x A B' := by
  have hsub : B - A ≤ B' - A := Nat.sub_le_sub_right hBB' A
  have hlog : 0 ≤ 1 + Real.log (((A + 1 : ℕ) : ℝ)) := by
    have : 0 ≤ Real.log (((A + 1 : ℕ) : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ A + 1 by omega))
    linarith
  unfold threeBranchBound
  gcongr

/-- Every partial sum of `(A,B]` is bounded by the full-interval packaged
majorant.  This is the exact interface required by Abel summation. -/
lemma norm_reciprocalExpSum_prefix_le_threeBranchBound
    (x : ℝ) (A B t : ℕ) (hx : 0 < x)
    (hAt : A ≤ t) (htB : t ≤ B)
    (hdyadic : B - A ≤ A + 1)
    (hone : 12 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 4) :
    ‖reciprocalExpSum x A t‖ ≤ threeBranchBound x A B := by
  by_cases hstrict : A < t
  · have htDyadic : t - A ≤ A + 1 :=
      (Nat.sub_le_sub_right htB A).trans hdyadic
    have h := norm_reciprocalExpSum_le_threeBranch
      x A t hx hstrict htDyadic hone
    exact h.trans (threeBranchBound_mono_upper hx hAt htB)
  · have ht : t = A := by omega
    subst t
    simp only [reciprocalExpSum, Finset.Ioc_self, Finset.sum_empty, norm_zero]
    exact threeBranchBound_nonneg A B hx

/-- Fully concrete three-branch estimate for an actual Vaughan inner sum.
This is the direct analytic endpoint used by the Type-I coefficient
assembly below. -/
lemma norm_vaughanInner_le_threeBranch
    (x : ℝ) (y y' m : ℕ) (hx : 0 < x) (hm : 1 ≤ m)
    (hAB : y / m < y' / m)
    (hdyadic : y' / m - y / m ≤ y / m + 1)
    (hone : 12 * (x / (m : ℝ)) ≤
      (((y / m) + 1 : ℕ) : ℝ) ^ 4) :
    ‖∑ l ∈ Finset.Ioc (y / m) (y' / m),
        Vaughan.reciprocalPhase x (m * l)‖ ≤
      (((y' / m + 1 : ℕ) : ℝ)) ^ 2 / (x / (m : ℝ)) +
      128 * (((y' / m - y / m : ℕ) : ℝ)) *
        ((x / (m : ℝ)) / (((y / m) + 1 : ℕ) : ℝ) ^ 4) ^
          (1 / 6 : ℝ) *
          Real.sqrt (1 + Real.log ((((y / m) + 1 : ℕ) : ℝ))) +
      16 * Real.sqrt (Real.sqrt (
        ((((y / m) + 1 : ℕ) : ℝ)) ^ 2 *
          Real.sqrt ((((y' / m - y / m : ℕ) : ℝ)) ^ 3) *
            (1 + Real.log ((((y / m) + 1 : ℕ) : ℝ))) ^ 2)) := by
  rw [vaughanInner_eq_reciprocalExpSum x y y' m hm]
  exact norm_reciprocalExpSum_le_threeBranch
    (x / (m : ℝ)) (y / m) (y' / m)
    (div_pos hx (by positivity)) hAB hdyadic hone

/-- Low-frequency (first derivative) bound for the same concrete Vaughan
inner sum. -/
lemma norm_vaughanInner_le_firstDerivative
    (x : ℝ) (y y' m : ℕ) (hx : 0 < x) (hm : 1 ≤ m)
    (hAB : y / m ≤ y' / m)
    (hhalf :
      (x / (m : ℝ)) / (((y / m) + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 2) :
    ‖∑ l ∈ Finset.Ioc (y / m) (y' / m),
        Vaughan.reciprocalPhase x (m * l)‖ ≤
      (((y' / m + 1 : ℕ) : ℝ)) ^ 2 / (x / (m : ℝ)) := by
  rw [vaughanInner_eq_reciprocalExpSum x y y' m hm]
  exact norm_reciprocalExpSum_le_firstDerivative
    (x / (m : ℝ)) (y / m) (y' / m)
    (div_pos hx (by positivity)) hAB hhalf

/-- Direct specialization of the proved two-step van der Corput estimate to
the actual Vaughan reciprocal phase on a product interval.  In particular,
this theorem has no abstract exponential-sum hypothesis: its conclusion is
an invocation of `reciprocalExpSum_fourth_le` with the phase parameter
rescaled from `x` to `x/m`. -/
lemma vaughanInner_fourth_le
    (x : ℝ) (y y' m q : ℕ) (hx : 0 < x) (hm : 1 ≤ m)
    (hAB : y / m ≤ y' / m) (hq : 1 ≤ q)
    (hqN : q ^ 2 ≤ y' / m - y / m)
    (hderiv :
      12 * (x / (m : ℝ)) * (q : ℝ) ^ 3 ≤
        (((y / m) + 1 : ℕ) : ℝ) ^ 4) :
    ‖∑ l ∈ Finset.Ioc (y / m) (y' / m),
        Vaughan.reciprocalPhase x (m * l)‖ ^ 4 ≤
      512 * (((y' / m - y / m : ℕ) : ℝ)) ^ 4 / (q : ℝ) ^ 2 +
        (512 : ℝ) * (((y' / m - y / m : ℕ) : ℝ)) ^ 3 *
            (((y' / m + 1 : ℕ) : ℝ)) ^ 4 /
              (6 * (x / (m : ℝ))) / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by
  rw [vaughanInner_eq_reciprocalExpSum x y y' m hm]
  exact reciprocalExpSum_fourth_le (x / (m : ℝ)) (y / m) (y' / m) q
    (div_pos hx (by positivity)) hAB hq hqN hderiv

/-- The `m`-dependent right hand side obtained by applying Proposition 8.1
with `k = 2` to the rescaled interval `(y/m,t]`. -/
noncomputable def proposition8TypeITerm (x y : ℝ) (m : ℕ) : ℝ :=
  32 * (2 * (x / (m : ℝ)) / (y / (m : ℝ)) ^ 4) ^ (1 / 6 : ℝ) *
    (y / (m : ℝ)) * Real.sqrt (Real.log (y / (m : ℝ)))

/-- A common numerator for all the rescaled Proposition 8.1 bounds with
`1 ≤ m ≤ M`.  The point of the next lemma is that the remaining dependence
on `m` is exactly harmonic. -/
noncomputable def proposition8TypeIMajorant (x y : ℝ) (M : ℕ) : ℝ :=
  32 * y * (2 * x * (M : ℝ) ^ 3 / y ^ 4) ^ (1 / 6 : ℝ) *
    Real.sqrt (Real.log y)

/-- The algebraic heart of the Type-I outer summation: after the phase and
interval are both divided by `m`, the Proposition 8.1 bound is `O(1/m)`.
This retains the paper's `M^3` inside the sixth root. -/
lemma proposition8TypeITerm_le_majorant_div
    {x y : ℝ} {m M : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hm : 1 ≤ m) (hmM : m ≤ M) (_hym : 1 ≤ y / (m : ℝ)) :
    proposition8TypeITerm x y m ≤
      proposition8TypeIMajorant x y M / (m : ℝ) := by
  have hmpos : (0 : ℝ) < m := by positivity
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le hmpos (by exact_mod_cast hmM)
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmMR : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hbase_m :
      2 * (x / (m : ℝ)) / (y / (m : ℝ)) ^ 4 =
        (2 * x / y ^ 4) * (m : ℝ) ^ 3 := by
    field_simp
  have hbase_M :
      2 * x * (M : ℝ) ^ 3 / y ^ 4 =
        (2 * x / y ^ 4) * (M : ℝ) ^ 3 := by ring
  have hconstant : 0 ≤ 2 * x / y ^ 4 := by positivity
  have hpow : (m : ℝ) ^ 3 ≤ (M : ℝ) ^ 3 := by gcongr
  have hbase :
      2 * (x / (m : ℝ)) / (y / (m : ℝ)) ^ 4 ≤
        2 * x * (M : ℝ) ^ 3 / y ^ 4 := by
    rw [hbase_m, hbase_M]
    exact mul_le_mul_of_nonneg_left hpow hconstant
  have hrpow :
      (2 * (x / (m : ℝ)) / (y / (m : ℝ)) ^ 4) ^ (1 / 6 : ℝ) ≤
        (2 * x * (M : ℝ) ^ 3 / y ^ 4) ^ (1 / 6 : ℝ) := by
    exact Real.rpow_le_rpow (by positivity) hbase (by norm_num)
  have hympos : 0 < y / (m : ℝ) := div_pos hy hmpos
  have hymle : y / (m : ℝ) ≤ y := by
    exact div_le_self hy.le hmone
  have hlog : Real.log (y / (m : ℝ)) ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn hympos hy hymle
  have hsqrt : Real.sqrt (Real.log (y / (m : ℝ))) ≤
      Real.sqrt (Real.log y) := Real.sqrt_le_sqrt hlog
  have hrewrite :
      proposition8TypeIMajorant x y M / (m : ℝ) =
        32 * (2 * x * (M : ℝ) ^ 3 / y ^ 4) ^ (1 / 6 : ℝ) *
          (y / (m : ℝ)) * Real.sqrt (Real.log y) := by
    unfold proposition8TypeIMajorant
    field_simp
  rw [proposition8TypeITerm, hrewrite]
  gcongr

/-- Sum a family whose `m`-th estimate has the harmonic shape `Q/m`. -/
lemma sum_Icc_le_mul_dyadicCount
    (P : ℕ → ℝ) {M : ℕ} {Q : ℝ} (hQ : 0 ≤ Q)
    (hP : ∀ m ∈ Finset.Icc 1 M, P m ≤ Q / (m : ℝ)) :
    (∑ m ∈ Finset.Icc 1 M, P m) ≤ Q * dyadicCount M := by
  calc
    (∑ m ∈ Finset.Icc 1 M, P m) ≤
        ∑ m ∈ Finset.Icc 1 M, Q / (m : ℝ) :=
      Finset.sum_le_sum hP
    _ = Q * ∑ m ∈ Finset.Icc 1 M, (m : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      simp only [div_eq_mul_inv]
    _ ≤ Q * dyadicCount M :=
      mul_le_mul_of_nonneg_left (sum_inv_le_dyadicCount M) hQ

/-- Closed summation of all three analytic branches. -/
lemma sum_threeBranchBound_le
    {x : ℝ} {y y' M : ℕ} (hx : 0 < x) (hM : 1 ≤ M)
    (hy' : y' ≤ 2 * y)
    (hA : ∀ m ∈ Finset.Icc 1 M, 1 ≤ y / m) :
    (∑ m ∈ Finset.Icc 1 M,
        threeBranchBound (x / (m : ℝ)) (y / m) (y' / m)) ≤
      threeBranchOuterNumerator x y M * dyadicCount M := by
  apply sum_Icc_le_mul_dyadicCount
    (fun m => threeBranchBound (x / (m : ℝ)) (y / m) (y' / m))
    (Q := threeBranchOuterNumerator x y M)
    (threeBranchOuterNumerator_nonneg y M hx)
  intro m hm
  have hm' := Finset.mem_Icc.mp hm
  exact threeBranchBound_le_outerNumerator_div hx hm'.1 hm'.2 (hA m hm) hy'

/-- Coefficient and inner-sum bounds for a concrete finite outer Type-I
sum.  This is the final triangle-inequality step after Lemma 9.2. -/
lemma norm_outerSum_le
    (c : ℕ → ℂ) (S : ℕ → ℂ) (P : ℕ → ℝ) {M : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hc : ∀ m ∈ Finset.Icc 1 M, ‖c m‖ ≤ C)
    (hS : ∀ m ∈ Finset.Icc 1 M, ‖S m‖ ≤ P m) :
    ‖∑ m ∈ Finset.Icc 1 M, c m * S m‖ ≤
      C * ∑ m ∈ Finset.Icc 1 M, P m := by
  calc
    ‖∑ m ∈ Finset.Icc 1 M, c m * S m‖ ≤
        ∑ m ∈ Finset.Icc 1 M, ‖c m * S m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M, C * P m := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul]
      exact mul_le_mul (hc m hm) (hS m hm) (norm_nonneg _) hC
    _ = C * ∑ m ∈ Finset.Icc 1 M, P m := by
      rw [Finset.mul_sum]

/-! ## The actual Vaughan Type-I coefficients -/

open scoped ArithmeticFunction

/-- Bound the paper's `Σ₁` after its exact Vaughan expansion. -/
lemma norm_sigma1_le_of_inner
    (y y' M : ℕ) (w : ℕ → ℂ) (P : ℕ → ℝ)
    (hinner : ∀ m ∈ Finset.Icc 1 M,
      ‖∑ l ∈ Finset.Ioc (y / m) (y' / m),
          (Real.log l : ℂ) * w (m * l)‖ ≤ P m) :
    ‖VaughanFourSums.sigma1 (Finset.Ioc y y') w M‖ ≤
      ∑ m ∈ Finset.Icc 1 M, P m := by
  rw [VaughanFourSums.sigma1_Ioc_eq_outer]
  have heq :
      (∑ m ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Ioc (y / m) (y' / m),
          (ArithmeticFunction.moebius m : ℂ) *
            (Real.log l : ℂ) * w (m * l)) =
        ∑ m ∈ Finset.Icc 1 M,
          (ArithmeticFunction.moebius m : ℂ) *
            (∑ l ∈ Finset.Ioc (y / m) (y' / m),
              (Real.log l : ℂ) * w (m * l)) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [heq]
  simpa using norm_outerSum_le
    (fun m => (ArithmeticFunction.moebius m : ℂ))
    (fun m => ∑ l ∈ Finset.Ioc (y / m) (y' / m),
      (Real.log l : ℂ) * w (m * l)) P
    (C := 1) (by norm_num)
    (by
      intro m hm
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m))
    hinner

/-- Bound the paper's `Σ₂,₁` using its actual coefficient
`b_r = ∑_{mk=r,m≤M,k≤K} μ(m)Λ(k)` and the proved estimate
`|b_r| ≤ log r ≤ log M`. -/
lemma norm_sigma21_le_of_inner
    (y y' M K : ℕ) (w : ℕ → ℂ) (P : ℕ → ℝ) (hM : 1 ≤ M)
    (hinner : ∀ r ∈ Finset.Icc 1 M,
      ‖∑ l ∈ Finset.Ioc (y / r) (y' / r), w (r * l)‖ ≤ P r) :
    ‖VaughanFourSums.sigma21 (Finset.Ioc y y') w M K‖ ≤
      Real.log M * ∑ r ∈ Finset.Icc 1 M, P r := by
  rw [VaughanFourSums.sigma21_Ioc_eq_outer]
  have heq :
      (∑ r ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Ioc (y / r) (y' / r),
          (VaughanFourSums.bCoeff M K r : ℂ) * w (r * l)) =
        ∑ r ∈ Finset.Icc 1 M,
          (VaughanFourSums.bCoeff M K r : ℂ) *
            (∑ l ∈ Finset.Ioc (y / r) (y' / r), w (r * l)) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
  rw [heq]
  apply norm_outerSum_le
  · exact Real.log_nonneg (by exact_mod_cast hM)
  · intro r hr
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (VaughanFourSums.abs_bCoeff_le_log M K r).trans ?_
    have hr' := Finset.mem_Icc.mp hr
    exact Real.strictMonoOn_log.monotoneOn
      (show (r : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        exact_mod_cast hr'.1)
      (show (M : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        exact_mod_cast hM)
      (by exact_mod_cast hr'.2)
  · exact hinner

/-- Assemble the two concrete Type-I pieces.  The only remaining input is a
pair of estimates for the displayed reciprocal inner sums; no abstract
`HasBlockEstimate` predicate occurs in the conclusion. -/
lemma norm_sigma1_add_sigma21_le_of_inner
    (y y' M K : ℕ) (w : ℕ → ℂ) (P : ℕ → ℝ) (L : ℝ)
    (hM : 1 ≤ M) (_hL : 0 ≤ L) (_hP : ∀ m, 0 ≤ P m)
    (hlogInner : ∀ m ∈ Finset.Icc 1 M,
      ‖∑ l ∈ Finset.Ioc (y / m) (y' / m),
          (Real.log l : ℂ) * w (m * l)‖ ≤ L * P m)
    (hinner : ∀ m ∈ Finset.Icc 1 M,
      ‖∑ l ∈ Finset.Ioc (y / m) (y' / m), w (m * l)‖ ≤ P m) :
    ‖VaughanFourSums.sigma1 (Finset.Ioc y y') w M‖ +
        ‖VaughanFourSums.sigma21 (Finset.Ioc y y') w M K‖ ≤
      (L + Real.log M) * ∑ m ∈ Finset.Icc 1 M, P m := by
  have h1 := norm_sigma1_le_of_inner y y' M w (fun m => L * P m) hlogInner
  have h21 := norm_sigma21_le_of_inner y y' M K w P hM hinner
  calc
    ‖VaughanFourSums.sigma1 (Finset.Ioc y y') w M‖ +
          ‖VaughanFourSums.sigma21 (Finset.Ioc y y') w M K‖ ≤
        (∑ m ∈ Finset.Icc 1 M, L * P m) +
          Real.log M * ∑ m ∈ Finset.Icc 1 M, P m := add_le_add h1 h21
    _ = (L + Real.log M) * ∑ m ∈ Finset.Icc 1 M, P m := by
      have hs : (∑ m ∈ Finset.Icc 1 M, L * P m) =
          L * ∑ m ∈ Finset.Icc 1 M, P m := by rw [Finset.mul_sum]
      rw [hs]
      ring

/-- Lemma 9.2 specialized to one of the paper's inner product intervals.
The harmless factor `2 log(2y)` is a coarse, rounding-stable replacement for
the paper's `log(y'^2/(my))`. -/
lemma norm_logInner_le_two_log
    (y y' m : ℕ) (w : ℕ → ℂ) (P : ℝ)
    (hA : 1 ≤ y / m) (hy' : y' ≤ 2 * y) (hP : 0 ≤ P)
    (hprefix : ∀ t, y / m ≤ t → t ≤ y' / m →
      ‖∑ l ∈ Finset.Ioc (y / m) t, w (m * l)‖ ≤ P) :
    ‖∑ l ∈ Finset.Ioc (y / m) (y' / m),
        (Real.log l : ℂ) * w (m * l)‖ ≤
      (2 * Real.log (2 * y : ℕ)) * P := by
  by_cases hAB : y / m < y' / m
  · have hraw := norm_logWeightedSum_le
      (fun l => w (m * l)) P hA hAB hP hprefix
    change ‖∑ l ∈ Finset.Ioc (y / m) (y' / m),
      Real.log (l : ℝ) • w (m * l)‖ ≤ _
    refine hraw.trans ?_
    apply mul_le_mul_of_nonneg_right ?_ hP
    let A := y / m
    let B := y' / m
    have hApos : (0 : ℝ) < A := by
      exact_mod_cast (show 0 < A by omega)
    have hBpos : (0 : ℝ) < B := by
      exact_mod_cast (show 0 < B by omega)
    have hAy : 0 ≤ Real.log (A : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hA)
    have hBle : B ≤ 2 * y := by
      dsimp [B]
      exact (Nat.div_le_self y' m).trans hy'
    have htwoYpos : (0 : ℝ) < (2 * y : ℕ) := by
      have hmpos : 0 < m := by
        by_contra hm
        have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        simp [hm0] at hA
      have hmy : m ≤ y := by
        have h := (Nat.le_div_iff_mul_le hmpos).mp hA
        simpa using h
      exact_mod_cast (show 0 < 2 * y by
        have : 0 < y := hmpos.trans_le hmy
        omega)
    have hlogB : Real.log (B : ℝ) ≤ Real.log (2 * y : ℕ) :=
      Real.strictMonoOn_log.monotoneOn hBpos htwoYpos (by exact_mod_cast hBle)
    have hAne : (A : ℝ) ≠ 0 := ne_of_gt hApos
    have hBne : (B : ℝ) ≠ 0 := ne_of_gt hBpos
    change Real.log (((B : ℝ) ^ 2) / (A : ℝ)) ≤
      2 * Real.log (2 * y : ℕ)
    calc
      Real.log (((B : ℝ) ^ 2) / (A : ℝ)) =
          2 * Real.log (B : ℝ) - Real.log (A : ℝ) := by
        rw [Real.log_div (pow_ne_zero 2 hBne) hAne, Real.log_pow]
        norm_num
      _ ≤ 2 * Real.log (B : ℝ) := sub_le_self _ hAy
      _ ≤ 2 * Real.log (2 * y : ℕ) :=
        mul_le_mul_of_nonneg_left hlogB (by norm_num)
  · have hempty : Finset.Ioc (y / m) (y' / m) = ∅ :=
      Finset.Ioc_eq_empty (by omega)
    rw [hempty]
    simp only [Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.log_nonneg (by
        have hypos : 0 < y := by
          by_contra hy0
          have : y = 0 := Nat.eq_zero_of_not_pos hy0
          simp [this] at hA
        exact_mod_cast (show 1 ≤ 2 * y by omega)))) hP

/-! ## Closed concrete Type-I estimate -/

/-- The actual `Σ₁ + Σ₂,₁` estimate obtained by combining Vaughan's
coefficients, the three proved reciprocal-sum branches, and Abel summation.
All hypotheses are explicit endpoint or derivative-range inequalities; in
particular there is no `HasBlockEstimate` or inner exponential-sum premise.

The finite sum on the right is intentionally left exact.  Its three terms
have respectively the first-derivative, sixth-root, and capped-shift shapes,
so later parameter specialization can sum each with the most convenient
elementary power estimate. -/
theorem norm_sigma1_add_sigma21_le_threeBranch
    (x : ℝ) (y y' M K : ℕ)
    (hx : 0 < x) (hM : 1 ≤ M) (hyy' : y ≤ y') (hy' : y' ≤ 2 * y)
    (hA : ∀ m ∈ Finset.Icc 1 M, 1 ≤ y / m)
    (hone : ∀ m ∈ Finset.Icc 1 M,
      12 * (x / (m : ℝ)) ≤ (((y / m) + 1 : ℕ) : ℝ) ^ 4) :
    ‖VaughanFourSums.sigma1 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M‖ +
      ‖VaughanFourSums.sigma21 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      (2 * Real.log (2 * y : ℕ) + Real.log M) *
        ∑ m ∈ Finset.Icc 1 M,
          threeBranchBound (x / (m : ℝ)) (y / m) (y' / m) := by
  have h1mem : 1 ∈ Finset.Icc 1 M := by simp [hM]
  have hyone : 1 ≤ y := by
    have := hA 1 h1mem
    simpa using this
  have hL : 0 ≤ 2 * Real.log (2 * y : ℕ) := by
    positivity
  have hP : ∀ m : ℕ, 0 ≤
      threeBranchBound (x / (m : ℝ)) (y / m) (y' / m) := by
    intro m
    unfold threeBranchBound
    positivity
  apply norm_sigma1_add_sigma21_le_of_inner
    y y' M K (Vaughan.reciprocalPhase x)
    (fun m => threeBranchBound (x / (m : ℝ)) (y / m) (y' / m))
    (2 * Real.log (2 * y : ℕ)) hM hL hP
  · intro m hm
    have hm' := Finset.mem_Icc.mp hm
    have hmpos : 0 < m := by omega
    apply norm_logInner_le_two_log y y' m
      (Vaughan.reciprocalPhase x)
      (threeBranchBound (x / (m : ℝ)) (y / m) (y' / m))
      (hA m hm) hy' (hP m)
    intro t hAt htB
    rw [vaughanProductInner_eq_reciprocalExpSum x (y / m) t m hm'.1]
    apply norm_reciprocalExpSum_prefix_le_threeBranchBound
      (x / (m : ℝ)) (y / m) (y' / m) t
      (div_pos hx (by exact_mod_cast hmpos)) hAt htB
      (quotient_interval_sub_le hm'.1 hy') (hone m hm)
  · intro m hm
    have hm' := Finset.mem_Icc.mp hm
    rw [vaughanProductInner_eq_reciprocalExpSum
      x (y / m) (y' / m) m hm'.1]
    apply norm_reciprocalExpSum_prefix_le_threeBranchBound
      (x / (m : ℝ)) (y / m) (y' / m) (y' / m)
      (div_pos hx (by exact_mod_cast (show 0 < m by omega)))
      (Nat.div_le_div_right hyy') le_rfl
      (quotient_interval_sub_le hm'.1 hy') (hone m hm)

/-- Fully summed Type-I endpoint in the global parameter range used by the
Granville--Ramaré assembly.  The right hand side contains no finite outer
sum and no analytic premise. -/
theorem norm_sigma1_add_sigma21_le_closed
    (x : ℝ) (y y' M K : ℕ)
    (hx : 0 < x) (hM : 1 ≤ M) (hMy : M ≤ y)
    (hyy' : y ≤ y') (hy' : y' ≤ 2 * y)
    (hglobal : 12 * x * (M : ℝ) ^ 3 ≤ (y : ℝ) ^ 4) :
    ‖VaughanFourSums.sigma1 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M‖ +
      ‖VaughanFourSums.sigma21 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      (2 * Real.log (2 * y : ℕ) + Real.log M) *
        (threeBranchOuterNumerator x y M * dyadicCount M) := by
  have hA : ∀ m ∈ Finset.Icc 1 M, 1 ≤ y / m := by
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    apply (Nat.le_div_iff_mul_le (show 0 < m by omega)).2
    simpa using hm'.2.trans hMy
  have hone : ∀ m ∈ Finset.Icc 1 M,
      12 * (x / (m : ℝ)) ≤ (((y / m) + 1 : ℕ) : ℝ) ^ 4 := by
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    exact scaled_fourth_derivative_condition hx.le hm'.1 hm'.2 hglobal
  have hraw := norm_sigma1_add_sigma21_le_threeBranch
    x y y' M K hx hM hyy' hy' hA hone
  refine hraw.trans ?_
  apply mul_le_mul_of_nonneg_left
    (sum_threeBranchBound_le hx hM hy' hA)
  exact add_nonneg
    (mul_nonneg (by norm_num) (Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2 * y by omega))))
    (Real.log_nonneg (by exact_mod_cast hM))

end PartialSummation

end Erdos175.TypeI
