/-
This file is derived from Gershon Bialer's ternary-Goldbach development.

The reused upstream material was released under the Apache License,
Version 2.0, as described in the file LICENSE. This file has been modified.
The upstream copyright and author notices are retained below.

Copyright (c) 2026 Gershon Bialer. All rights reserved.
-/

/-
# Abel summation (partial summation) — discrete number-theoretic form

Mathlib provides:

* `Finset.sum_Ico_by_parts`, `Finset.sum_Ioc_by_parts`,
  `Finset.sum_range_by_parts` — algebraic summation-by-parts in the
  shape `f n • G n − …` where `G k = ∑ i ∈ range k, g i` is a partial
  sum starting from `0`.
* `sum_mul_eq_sub_sub_integral_mul` and friends in
  `Mathlib/NumberTheory/AbelSummation.lean` — *continuous* Abel
  summation involving `deriv f` and an interval integral.

For the Vinogradov circle-method machinery (`S_Lambda_local_approximation`
M1, `typeI_sum_minor_arc_bound` m3, `vaughan_identity_finite` m2) we
repeatedly need the **purely discrete** Abel/partial-summation identity
in which the partial sums are over `Finset.Ioc M k` (an "offset by `M`"
shape), not over `Finset.range k`.  Concretely:

```
∑ n ∈ Ioc M N, a n * b n
  = (∑ n ∈ Ioc M N, a n) * b N
  − ∑ k ∈ Ioc M (N-1), (∑ n ∈ Ioc M k, a n) * (b (k+1) − b k)
```

together with an immediate norm bound that is convenient for absolute-
value/`bigO` estimates downstream.  Both are proved here from first
principles by induction on `N`.
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Module.Basic

namespace MathExtras
namespace AbelSummation

open Finset

/-! ### The basic algebraic identity -/

/-- **Abel's summation formula (Ioc, offset form).**

Let `a, b : ℕ → R` be sequences in a commutative ring.  For any
`M ≤ N`, writing `A(k) := ∑_{n ∈ (M,k]} a n` for the partial sums of
`a` starting from `M`, we have

```
∑_{n ∈ (M,N]} a n · b n
  = A(N) · b N − ∑_{k ∈ (M,N-1]} A(k) · (b(k+1) − b k).
```

This is the standard "summation by parts" identity in the shape that
arises in analytic-number-theory bounds, where one bounds a sum
`∑ a(n) b(n)` against the supremum of the partial sums of `a` and the
total variation of `b`. -/
theorem abel_summation_Ioc {R : Type*} [CommRing R]
    (a b : ℕ → R) (M N : ℕ) (hMN : M ≤ N) :
    ∑ n ∈ Finset.Ioc M N, a n * b n =
      (∑ n ∈ Finset.Ioc M N, a n) * b N
        - ∑ k ∈ Finset.Ioc M (N - 1),
            (∑ n ∈ Finset.Ioc M k, a n) * (b (k + 1) - b k) := by
  induction N, hMN using Nat.le_induction with
  | base =>
      simp
  | succ N hMN ih =>
      -- LHS: peel off the top term n = N+1.
      rw [Finset.sum_Ioc_succ_top hMN, Finset.sum_Ioc_succ_top hMN,
          Nat.add_sub_cancel]
      rcases Nat.eq_or_lt_of_le hMN with hMN' | hMN'
      · -- M = N: Ioc M N = ∅, Ioc M (N-1) = ∅; the identity collapses.
        subst hMN'
        simp
      · -- M < N: split the new "inner" sum over Ioc M N off its top k = N.
        have hN1 : M ≤ N - 1 := Nat.le_sub_one_of_lt hMN'
        have hNsub : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.one_le_of_lt hMN')
        have hsplit :
            ∑ k ∈ Finset.Ioc M N,
                (∑ n ∈ Finset.Ioc M k, a n) * (b (k + 1) - b k)
              = (∑ k ∈ Finset.Ioc M (N - 1),
                    (∑ n ∈ Finset.Ioc M k, a n) * (b (k + 1) - b k))
                + (∑ n ∈ Finset.Ioc M N, a n) * (b (N + 1) - b N) := by
          have h := Finset.sum_Ioc_succ_top (a := M) (b := N - 1) hN1
            (f := fun k => (∑ n ∈ Finset.Ioc M k, a n) * (b (k + 1) - b k))
          rw [hNsub] at h
          exact h
        rw [hsplit, ih]
        ring

/-! ### Complex-valued specialization -/

/-- Complex-valued version of `abel_summation_Ioc`, useful for
additive-character estimates `b(n) = e(αn)`. -/
theorem abel_summation_Ioc_complex
    (a b : ℕ → ℂ) (M N : ℕ) (hMN : M ≤ N) :
    ∑ n ∈ Finset.Ioc M N, a n * b n =
      (∑ n ∈ Finset.Ioc M N, a n) * b N
        - ∑ k ∈ Finset.Ioc M (N - 1),
            (∑ n ∈ Finset.Ioc M k, a n) * (b (k + 1) - b k) :=
  abel_summation_Ioc (R := ℂ) a b M N hMN

/-! ### Helper: telescoping a `(b k - b (k+1))` sum over `Ioc M (N-1)` -/

/-- Telescoping identity used in the Abel-summation norm bound:
`∑_{k ∈ (M, N-1]} (b k − b(k+1)) = b(M+1) − b N`, provided `M < N`. -/
lemma telescope_Ioc_sub (b : ℕ → ℝ) {M N : ℕ} (hMN : M < N) :
    ∑ k ∈ Finset.Ioc M (N - 1), (b k - b (k + 1)) = b (M + 1) - b N := by
  -- Rewrite Ioc M (N-1) as Ico (M+1) N.
  have hN1 : 1 ≤ N := Nat.one_le_of_lt hMN
  have hNsub : N - 1 + 1 = N := Nat.sub_add_cancel hN1
  have hrw : Finset.Ioc M (N - 1) = Finset.Ico (M + 1) N := by
    rw [← Ico_add_one_add_one_eq_Ioc, hNsub]
  rw [hrw, Finset.sum_Ico_eq_sum_range]
  -- Now ∑ i ∈ range (N - (M+1)), (b (M+1+i) - b (M+1+i+1)) = b(M+1) - b N
  -- using `Finset.sum_range_sub'` with `f := fun i => b (M+1+i)`.
  have hkey :
      ∑ i ∈ Finset.range (N - (M + 1)), (b (M + 1 + i) - b (M + 1 + (i + 1)))
        = b (M + 1) - b (M + 1 + (N - (M + 1))) := by
    have := Finset.sum_range_sub' (fun i => b (M + 1 + i)) (N - (M + 1))
    -- `sum_range_sub' f n = f 0 - f n`
    simpa using this
  have hcollapse : M + 1 + (N - (M + 1)) = N := by
    have hM1N : M + 1 ≤ N := hMN
    omega
  -- Align the summand: b (M+1+i) - b (M+1+i+1) = b (M+1+i) - b (M+1+(i+1)).
  have hcongr :
      ∀ i ∈ Finset.range (N - (M + 1)),
        b (M + 1 + i) - b (M + 1 + i + 1)
          = b (M + 1 + i) - b (M + 1 + (i + 1)) := by
    intro i _
    rfl
  rw [Finset.sum_congr rfl hcongr, hkey, hcollapse]

/-! ### Norm bound (monotone-weight corollary) -/

/-- **Abel-summation norm bound (monotone nonnegative real weight).**

Let `a : ℕ → ℂ` and let `b : ℕ → ℝ` be nonnegative everywhere and
*monotonically decreasing* on `[M, N]`.  If every partial sum
`‖∑_{n ∈ (M,k]} a n‖ ≤ A` for all `k ∈ (M, N]`, and `A ≥ 0`, then

```
‖∑ n ∈ Ioc M N, a n · (b n : ℂ)‖  ≤  A · b (M + 1).
```

This is the discrete analogue of the elementary bound
`|∫ f g'| ≤ (sup |F|) · |g(b) − g(a)|` for monotone `g`, and is the
form of Abel's inequality most directly useful for the Type I / Type II
estimates that feed `S_Lambda_local_approximation` and
`typeI_sum_minor_arc_bound`. -/
theorem abel_norm_bound_monotone_decreasing
    (a : ℕ → ℂ) (b : ℕ → ℝ) (M N : ℕ) (hMN : M ≤ N)
    (A : ℝ) (hA_nonneg : 0 ≤ A)
    (hA : ∀ k ∈ Finset.Ioc M N, ‖∑ n ∈ Finset.Ioc M k, a n‖ ≤ A)
    (hb_nonneg : ∀ k, 0 ≤ b k)
    (hb_dec : ∀ k, M ≤ k → k < N → b (k + 1) ≤ b k) :
    ‖∑ n ∈ Finset.Ioc M N, a n * (b n : ℂ)‖ ≤ A * b (M + 1) := by
  -- Step 1: Abel summation.
  rw [abel_summation_Ioc_complex a (fun n => (b n : ℂ)) M N hMN]
  -- Local abbreviation.
  set Apart : ℕ → ℂ := fun k => ∑ n ∈ Finset.Ioc M k, a n with hApart_def
  -- Per-difference bound: ‖((b(k+1) - b k : ℂ))‖ = b k - b(k+1) when monotone dec.
  have hnorm_diff_eq :
      ∀ k, M ≤ k → k < N →
        ‖((b (k + 1) : ℂ) - (b k : ℂ))‖ = b k - b (k + 1) := by
    intro k hMk hkN
    have hdiff_le : b (k + 1) - b k ≤ 0 := sub_nonpos.mpr (hb_dec k hMk hkN)
    have hcast : ((b (k + 1) : ℂ) - (b k : ℂ)) = ((b (k + 1) - b k : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hdiff_le]
    ring
  -- Step 2: triangle inequality.
  refine le_trans (norm_sub_le _ _) ?_
  -- ‖Apart N · (b N : ℂ)‖ ≤ ‖Apart N‖ · b N (using b N ≥ 0).
  have hbnd_top :
      ‖Apart N * (b N : ℂ)‖ ≤ ‖Apart N‖ * b N := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb_nonneg N)]
  -- Bound the "remainder" sum.
  have hbnd_rem :
      ‖∑ k ∈ Finset.Ioc M (N - 1),
          Apart k * ((b (k + 1) : ℂ) - (b k : ℂ))‖
        ≤ ∑ k ∈ Finset.Ioc M (N - 1),
            ‖Apart k‖ * (b k - b (k + 1)) := by
    refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro k hk
    rw [norm_mul]
    have hkmem := hk
    obtain ⟨hMk, hkN1⟩ := Finset.mem_Ioc.mp hkmem
    -- We need k < N to apply hnorm_diff_eq.
    have hkN : k < N := by
      rcases Nat.eq_zero_or_pos N with hN0 | hN0
      · subst hN0
        simp at hkmem
      · omega
    rw [hnorm_diff_eq k (le_of_lt hMk) hkN]
  -- Combine the two pieces.
  have hcombine :
      ‖Apart N * (b N : ℂ)‖
        + ‖∑ k ∈ Finset.Ioc M (N - 1),
              Apart k * ((b (k + 1) : ℂ) - (b k : ℂ))‖
        ≤ ‖Apart N‖ * b N
          + ∑ k ∈ Finset.Ioc M (N - 1),
              ‖Apart k‖ * (b k - b (k + 1)) := add_le_add hbnd_top hbnd_rem
  refine le_trans hcombine ?_
  -- Step 3: bound each ‖Apart …‖ by A, then telescope.
  rcases Nat.eq_or_lt_of_le hMN with hMN' | hMN'
  · -- M = N: Apart N = 0; Ioc M (N-1) = ∅.
    subst hMN'
    have hAp_zero : Apart M = 0 := by
      simp [hApart_def]
    simp [hAp_zero]
    exact mul_nonneg hA_nonneg (hb_nonneg _)
  · -- M < N: substantive case.
    have hApN : ‖Apart N‖ ≤ A := hA N (Finset.mem_Ioc.mpr ⟨hMN', le_rfl⟩)
    have hApk : ∀ k ∈ Finset.Ioc M (N - 1), ‖Apart k‖ ≤ A := by
      intro k hk
      obtain ⟨hMk, hkN1⟩ := Finset.mem_Ioc.mp hk
      have hkN : k ≤ N := le_trans hkN1 (Nat.sub_le _ _)
      exact hA k (Finset.mem_Ioc.mpr ⟨hMk, hkN⟩)
    -- ‖Apart N‖ · b N ≤ A · b N.
    have h1 : ‖Apart N‖ * b N ≤ A * b N :=
      mul_le_mul_of_nonneg_right hApN (hb_nonneg _)
    -- ∑ ‖Apart k‖ · (b k − b(k+1)) ≤ ∑ A · (b k − b(k+1)).
    have hdiff_nonneg : ∀ k ∈ Finset.Ioc M (N - 1), 0 ≤ b k - b (k + 1) := by
      intro k hk
      obtain ⟨hMk, hkN1⟩ := Finset.mem_Ioc.mp hk
      have hkN : k < N := by
        have hN1 : 1 ≤ N := Nat.one_le_of_lt hMN'
        omega
      exact sub_nonneg.mpr (hb_dec k (le_of_lt hMk) hkN)
    have h2 :
        ∑ k ∈ Finset.Ioc M (N - 1), ‖Apart k‖ * (b k - b (k + 1))
          ≤ ∑ k ∈ Finset.Ioc M (N - 1), A * (b k - b (k + 1)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right (hApk k hk) (hdiff_nonneg k hk)
    have h3 :
        ∑ k ∈ Finset.Ioc M (N - 1), A * (b k - b (k + 1))
          = A * (b (M + 1) - b N) := by
      rw [← Finset.mul_sum, telescope_Ioc_sub b hMN']
    -- Now: A·b(N) + A·(b(M+1) - b N) = A·b(M+1).
    calc ‖Apart N‖ * b N
            + ∑ k ∈ Finset.Ioc M (N - 1), ‖Apart k‖ * (b k - b (k + 1))
          ≤ A * b N
              + ∑ k ∈ Finset.Ioc M (N - 1), A * (b k - b (k + 1)) := by
            exact add_le_add h1 h2
      _ = A * b N + A * (b (M + 1) - b N) := by rw [h3]
      _ = A * b (M + 1) := by ring

/-! ### Norm bound (bounded-variation weight, no monotonicity required) -/

/-- **Abel-summation norm bound for a bounded-variation real weight.**

The monotone corollary `abel_norm_bound_monotone_decreasing` requires the weight
`b` to be nonincreasing, which fails for *unimodal* kernels such as the dilated
smoothing profile `m ↦ η◦(d·m/x)`.  This corollary replaces the monotonicity
hypothesis by a uniform bound `TV` on the **total variation** of `b` over the range,

```
∑_{k ∈ (M, N-1]} |b (k+1) − b k|  ≤  TV,
```

and concludes

```
‖∑ n ∈ Ioc M N, a n · (b n : ℂ)‖  ≤  A · (|b N| + TV).
```

This is the discrete analogue of `|∫ f g'| ≤ (sup|F|) · TV(g)` and is the Abel form
used by the §3.4 tight Type-I block bounds, where `A` is the sup of the partial sums
`B(k)` of the truncated-von-Mangoldt weight and `TV = 2` is supplied by the unimodal
total-variation bound `eta_circ_tv_grid_le`. -/
theorem abel_norm_bound_boundedVariation
    (a : ℕ → ℂ) (b : ℕ → ℝ) (M N : ℕ) (hMN : M ≤ N)
    (A : ℝ) (hA_nonneg : 0 ≤ A)
    (hA : ∀ k ∈ Finset.Ioc M N, ‖∑ n ∈ Finset.Ioc M k, a n‖ ≤ A)
    (TV : ℝ)
    (hTV : ∑ k ∈ Finset.Ioc M (N - 1), |b (k + 1) - b k| ≤ TV) :
    ‖∑ n ∈ Finset.Ioc M N, a n * (b n : ℂ)‖ ≤ A * (|b N| + TV) := by
  -- Step 1: Abel summation.
  rw [abel_summation_Ioc_complex a (fun n => (b n : ℂ)) M N hMN]
  set Apart : ℕ → ℂ := fun k => ∑ n ∈ Finset.Ioc M k, a n with hApart_def
  -- Triangle inequality on the two pieces.
  refine le_trans (norm_sub_le _ _) ?_
  -- Top term: ‖Apart N · (b N : ℂ)‖ ≤ A · |b N|.
  have hApN : ‖Apart N‖ ≤ A := by
    rcases Nat.eq_or_lt_of_le hMN with hMN' | hMN'
    · subst hMN'; simp [hApart_def]; exact hA_nonneg
    · exact hA N (Finset.mem_Ioc.mpr ⟨hMN', le_rfl⟩)
  have hbnd_top : ‖Apart N * (b N : ℂ)‖ ≤ A * |b N| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hApN le_rfl (abs_nonneg _) hA_nonneg
  -- Remainder term: ‖∑ Apart k · (b(k+1)-b k)‖ ≤ A · ∑ |b(k+1)-b k| ≤ A · TV.
  have hbnd_rem :
      ‖∑ k ∈ Finset.Ioc M (N - 1),
          Apart k * ((b (k + 1) : ℂ) - (b k : ℂ))‖
        ≤ A * ∑ k ∈ Finset.Ioc M (N - 1), |b (k + 1) - b k| := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    obtain ⟨hMk, hkN1⟩ := Finset.mem_Ioc.mp hk
    have hkN : k ≤ N := le_trans hkN1 (Nat.sub_le _ _)
    have hApk : ‖Apart k‖ ≤ A := hA k (Finset.mem_Ioc.mpr ⟨hMk, hkN⟩)
    rw [norm_mul]
    have hcast : ‖((b (k + 1) : ℂ) - (b k : ℂ))‖ = |b (k + 1) - b k| := by
      rw [show ((b (k + 1) : ℂ) - (b k : ℂ)) = ((b (k + 1) - b k : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
    rw [hcast]
    exact mul_le_mul hApk le_rfl (abs_nonneg _) hA_nonneg
  -- TV bound on the remainder.
  have hrem_TV :
      ‖∑ k ∈ Finset.Ioc M (N - 1),
          Apart k * ((b (k + 1) : ℂ) - (b k : ℂ))‖ ≤ A * TV :=
    le_trans hbnd_rem (mul_le_mul_of_nonneg_left hTV hA_nonneg)
  -- Combine and distribute.
  calc ‖Apart N * (b N : ℂ)‖
        + ‖∑ k ∈ Finset.Ioc M (N - 1), Apart k * ((b (k + 1) : ℂ) - (b k : ℂ))‖
      ≤ A * |b N| + A * TV := add_le_add hbnd_top hrem_TV
    _ = A * (|b N| + TV) := by ring

end AbelSummation
end MathExtras
