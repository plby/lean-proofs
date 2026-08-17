/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import ErdosProblems.Erdos543.LowRankCount
import ErdosProblems.Erdos543.Moments

/-!
# Quantitative finite bounds for factorial moments

This file is the numerical layer of the factorial-moment argument for
Erdos Problem 543.  It deliberately separates the exact incidence-matrix
enumeration from the elementary estimates which are subsequently applied to
that enumeration.

The main ingredients are:

* an explicit relative comparison between a descending factorial and a power;
* a bound for a rank-stratified low-rank contribution from pointwise incidence
  counts;
* an explicit bound for the loss in the full-rank contribution; and
* a final two-sided relative-error lemma which combines the full- and low-rank
  pieces.

All statements are finite and have explicit hypotheses.  In particular, no
asymptotic estimate is assumed in this file.
-/

open scoped BigOperators
open Finset

namespace Erdos543

attribute [local instance] Classical.propDecidable

/-! ## Descending factorial versus a power -/

/-- A convenient lower bound obtained by replacing every factor in the
descending factorial by `M - r`. -/
lemma pow_sub_le_descFactorial (M r : ℕ) :
    (M - r) ^ r ≤ M.descFactorial r := by
  exact (Nat.pow_le_pow_left (Nat.sub_le_sub_right (Nat.le_succ M) r) r).trans
    (Nat.pow_sub_le_descFactorial M r)

/-- An additive form of the elementary estimate
`(M)_r = M^r (1 + O(r^2/M))`.  The deliberately coarse constant `1` is
particularly useful because it requires no logarithms. -/
lemma pow_le_descFactorial_add_error {M r : ℕ} (hr : r ≤ M) :
    M ^ r ≤ M.descFactorial r + r * r * M ^ (r - 1) := by
  have hsub : (M - r : ℕ) ^ r ≤ M.descFactorial r :=
    pow_sub_le_descFactorial M r
  have hcastsub : ((M - r : ℕ) : ℝ) = (M : ℝ) - r := by
    rw [Nat.cast_sub hr]
  have hpowdiff :
      (M : ℝ) ^ r - ((M - r : ℕ) : ℝ) ^ r ≤
        (r : ℝ) * r * (M : ℝ) ^ (r - 1) := by
    have habs := abs_pow_sub_pow_le (M : ℝ) ((M - r : ℕ) : ℝ) r
    rw [hcastsub] at habs
    have hM0 : (0 : ℝ) ≤ M := by positivity
    have hsub0 : (0 : ℝ) ≤ (M : ℝ) - r := by
      rw [← hcastsub]
      positivity
    have hmax : max |(M : ℝ)| |(M : ℝ) - r| = (M : ℝ) := by
      rw [abs_of_nonneg hM0, abs_of_nonneg hsub0, max_eq_left]
      linarith
    rw [hmax] at habs
    have hrnonneg : (0 : ℝ) ≤ (r : ℝ) := by positivity
    simp only [sub_sub_cancel, abs_of_nonneg hrnonneg] at habs
    have hdiff0 : 0 ≤ (M : ℝ) ^ r - ((M : ℝ) - r) ^ r := by
      exact sub_nonneg.mpr (pow_le_pow_left₀ hsub0 (by linarith) r)
    rw [abs_of_nonneg hdiff0] at habs
    simpa [hcastsub, mul_assoc] using habs
  have hreal :
      (M : ℝ) ^ r ≤ (M.descFactorial r : ℝ) +
        (r : ℝ) * r * (M : ℝ) ^ (r - 1) := by
    calc
      (M : ℝ) ^ r ≤ ((M - r : ℕ) : ℝ) ^ r +
          (r : ℝ) * r * (M : ℝ) ^ (r - 1) := by linarith
      _ ≤ (M.descFactorial r : ℝ) +
          (r : ℝ) * r * (M : ℝ) ^ (r - 1) :=
        by
          simpa only [Nat.cast_pow, add_comm] using
            (add_le_add_right (Nat.cast_le.mpr hsub)
              ((r : ℝ) * r * (M : ℝ) ^ (r - 1)))
  exact_mod_cast hreal

/-- The descending factorial differs from the corresponding power by at most
`r^2 M^(r-1)`. -/
lemma abs_descFactorial_sub_pow_le {M r : ℕ} (hr : r ≤ M) :
    |(M.descFactorial r : ℝ) - (M : ℝ) ^ r| ≤
      (r : ℝ) ^ 2 * (M : ℝ) ^ (r - 1) := by
  have hu : (M.descFactorial r : ℝ) ≤ (M : ℝ) ^ r := by
    exact_mod_cast Nat.descFactorial_le_pow M r
  have hl : (M : ℝ) ^ r ≤ (M.descFactorial r : ℝ) +
      (r : ℝ) * r * (M : ℝ) ^ (r - 1) := by
    exact_mod_cast pow_le_descFactorial_add_error hr
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  nlinarith [pow_two_nonneg (r : ℝ),
    pow_nonneg (show (0 : ℝ) ≤ (M : ℝ) by positivity) (r - 1)]

/-- Relative form of `abs_descFactorial_sub_pow_le`. -/
lemma abs_descFactorial_div_pow_sub_one_le {M r : ℕ}
    (hM : 0 < M) (hr : r ≤ M) :
    |(M.descFactorial r : ℝ) / (M : ℝ) ^ r - 1| ≤
      (r : ℝ) ^ 2 / M := by
  have hMp : (0 : ℝ) < (M : ℝ) ^ r := pow_pos (by exact_mod_cast hM) r
  have h := abs_descFactorial_sub_pow_le hr
  rw [div_sub_one hMp.ne', abs_div, abs_of_pos hMp]
  calc
    |(M.descFactorial r : ℝ) - (M : ℝ) ^ r| / (M : ℝ) ^ r ≤
        ((r : ℝ) ^ 2 * (M : ℝ) ^ (r - 1)) / (M : ℝ) ^ r :=
      div_le_div_of_nonneg_right h hMp.le
    _ = (r : ℝ) ^ 2 / M := by
      by_cases hr0 : r = 0
      · simp [hr0]
      · rw [← pow_sub_one_mul hr0 (M : ℝ)]
        have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
        have hMpowne : (M : ℝ) ^ r ≠ 0 := hMp.ne'
        field_simp [hMne, hMpowne]

/-! ## Rank-stratified low-rank contributions -/

/-- Contribution of rational ranks `1,...,r-1` to a factorial moment.  The
function `C d` is the number of consistent target/incidence systems of rank
`d`; division by `p^d` is the finite-field fiber probability. -/
noncomputable def lowRankContribution (p r : ℕ) (C : ℕ → ℕ) : ℝ :=
  ∑ d ∈ Ico 1 r, (C d : ℝ) / (p : ℝ) ^ d

/-- The explicit majorant obtained from the `3/4` Boolean-cube loss.  In the
application, `m` is the number of targets (one or two), `2^k` is the size of
the entire Boolean cube, and `2^(r^2)` counts possible column spans. -/
noncomputable def incidenceLowRankEnvelope
    (p k r m : ℕ) : ℝ :=
  (m : ℝ) ^ r * (2 : ℝ) ^ (r * r) * ((3 : ℝ) / 4) ^ k *
    ∑ d ∈ Ico 1 r, (((2 : ℝ) ^ k) / p) ^ d

lemma lowRankContribution_nonneg (p r : ℕ) (C : ℕ → ℕ) :
    0 ≤ lowRankContribution p r C := by
  apply Finset.sum_nonneg
  intro d hd
  positivity

/-- Pointwise incidence-pattern estimates sum to the expected geometric
majorant.  This is the exact finite inequality used after the hypercube
intersection estimate. -/
lemma lowRankContribution_le_geometric
    {p r : ℕ} {C : ℕ → ℕ} {A H q : ℝ}
    (hp : 0 < p) (_hA : 0 ≤ A) (_hH : 0 ≤ H) (_hq : 0 ≤ q)
    (hC : ∀ d ∈ Ico 1 r, (C d : ℝ) ≤ A * H * q ^ d) :
    lowRankContribution p r C ≤
      A * H * ∑ d ∈ Ico 1 r, (q / p) ^ d := by
  rw [lowRankContribution, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  calc
    (C d : ℝ) / (p : ℝ) ^ d ≤
        (A * H * q ^ d) / (p : ℝ) ^ d := by
      exact div_le_div_of_nonneg_right (hC d hd) (pow_nonneg hpR.le d)
    _ = A * H * (q / p) ^ d := by rw [div_pow]; ring

/-- Specialized form of `lowRankContribution_le_geometric` matching the
incidence-matrix count in the Ma--Tang argument. -/
lemma lowRankContribution_le_incidenceEnvelope
    {p k r m : ℕ} {C : ℕ → ℕ} (hp : 0 < p)
    (hC : ∀ d ∈ Ico 1 r,
      (C d : ℝ) ≤ (m : ℝ) ^ r * (2 : ℝ) ^ (r * r) *
        ((3 : ℝ) / 4) ^ k * (((2 : ℝ) ^ k) ^ d)) :
    lowRankContribution p r C ≤ incidenceLowRankEnvelope p k r m := by
  simpa [incidenceLowRankEnvelope, mul_assoc] using
    (lowRankContribution_le_geometric (C := C) hp
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg m) r) (by positivity))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) k)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)
      (fun d hd ↦ by simpa [mul_assoc] using hC d hd))

/-- A coarse finite bound for the geometric sum when its ratio is at least
one.  There are fewer than `r` low-rank strata and every term is at most the
last possible one. -/
lemma sum_Ico_pow_le {x : ℝ} {r : ℕ} (hx : 1 ≤ x) :
    (∑ d ∈ Ico 1 r, x ^ d) ≤ r * x ^ (r - 1) := by
  calc
    (∑ d ∈ Ico 1 r, x ^ d) ≤ ∑ _d ∈ Ico 1 r, x ^ (r - 1) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdr' := (Finset.mem_Ico.mp hd).2
      have hdr : d ≤ r - 1 := by omega
      exact pow_le_pow_right₀ hx hdr
    _ = ((Ico 1 r).card : ℝ) * x ^ (r - 1) := by simp
    _ ≤ r * x ^ (r - 1) := by
      exact mul_le_mul_of_nonneg_right (by simp) (pow_nonneg (by linarith) _)

/-- Geometric majorant with its sum eliminated. -/
lemma lowRankContribution_le_last
    {p r : ℕ} {C : ℕ → ℕ} {A H q : ℝ}
    (hp : 0 < p) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hqp : (p : ℝ) ≤ q)
    (hC : ∀ d ∈ Ico 1 r, (C d : ℝ) ≤ A * H * q ^ d) :
    lowRankContribution p r C ≤
      A * H * r * (q / p) ^ (r - 1) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hq : 0 ≤ q := le_trans (by positivity) hqp
  calc
    lowRankContribution p r C ≤
        A * H * ∑ d ∈ Ico 1 r, (q / p) ^ d :=
      lowRankContribution_le_geometric hp hA hH hq hC
    _ ≤ A * H * (r * (q / p) ^ (r - 1)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ico_pow_le (by
          apply (le_div_iff₀ hpR).2
          simpa using hqp))
        (mul_nonneg hA hH)
    _ = A * H * r * (q / p) ^ (r - 1) := by ring

/-- The incidence envelope is at most its last geometric term when
`p ≤ 2^k`. -/
lemma incidenceLowRankEnvelope_le_last
    {p k r m : ℕ} (hp : 0 < p) (hpq : (p : ℝ) ≤ (2 : ℝ) ^ k) :
    incidenceLowRankEnvelope p k r m ≤
      (m : ℝ) ^ r * (2 : ℝ) ^ (r * r) * ((3 : ℝ) / 4) ^ k * r *
        (((2 : ℝ) ^ k / p) ^ (r - 1)) := by
  rw [incidenceLowRankEnvelope]
  have hratio : (1 : ℝ) ≤ (2 : ℝ) ^ k / p := by
    apply (le_div_iff₀ (show (0 : ℝ) < (p : ℝ) by exact_mod_cast hp)).2
    simpa using hpq
  have hmul : 0 ≤
      (m : ℝ) ^ r * (2 : ℝ) ^ (r * r) * ((3 : ℝ) / 4) ^ k := by
    positivity
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left (sum_Ico_pow_le (r := r) hratio) hmul)

/-! ## Counting all lower-rank incidence patterns -/

/-- Total number of incidence patterns in ranks `1,...,r-1`. -/
noncomputable def lowerRankPatternCount (r : ℕ) (T : ℕ → ℕ) : ℕ :=
  ∑ d ∈ Ico 1 r, T d

/-- The trivial rank-`d` estimate
`T_d ≤ 2^(r^2) (2^k)^d`, summed over all lower ranks. -/
lemma lowerRankPatternCount_le_last
    {k r : ℕ} {T : ℕ → ℕ}
    (hT : ∀ d ∈ Ico 1 r,
      T d ≤ 2 ^ (r * r) * (2 ^ k) ^ d) :
    lowerRankPatternCount r T ≤
      r * 2 ^ (r * r) * (2 ^ k) ^ (r - 1) := by
  rw [lowerRankPatternCount]
  calc
    (∑ d ∈ Ico 1 r, T d) ≤
        ∑ _d ∈ Ico 1 r, 2 ^ (r * r) * (2 ^ k) ^ (r - 1) := by
      apply Finset.sum_le_sum
      intro d hd
      refine (hT d hd).trans ?_
      have hdr' := (Finset.mem_Ico.mp hd).2
      have hdr : d ≤ r - 1 := by omega
      exact Nat.mul_le_mul_left (2 ^ (r * r))
        (Nat.pow_le_pow_right (show 0 < 2 ^ k by positivity) hdr)
    _ = (Ico 1 r).card * (2 ^ (r * r) * (2 ^ k) ^ (r - 1)) := by simp
    _ ≤ r * 2 ^ (r * r) * (2 ^ k) ^ (r - 1) := by
      have hc : (Ico 1 r).card ≤ r := by simp
      nlinarith [Nat.zero_le (2 ^ (r * r) * (2 ^ k) ^ (r - 1))]

/-! ## Full-rank loss and combination -/

/-- If `F` full-rank patterns and `L` lower-rank patterns partition all
ordered injective `r`-tuples from an `M`-element family, their deficit from
`M^r` is controlled by the collision error `r^2 M^(r-1)` and by `L`. -/
lemma fullRank_count_deficit {M r F L : ℕ} (hr : r ≤ M)
    (hpartition : F + L = M.descFactorial r) :
    (M : ℝ) ^ r - F ≤
      (r : ℝ) ^ 2 * (M : ℝ) ^ (r - 1) + L := by
  have hfall := pow_le_descFactorial_add_error hr
  rw [← hpartition] at hfall
  have hfallR : (M : ℝ) ^ r ≤ F + L +
      (r : ℝ) * r * (M : ℝ) ^ (r - 1) := by exact_mod_cast hfall
  nlinarith

/-- The full-rank contribution is never larger than the independent leading
term. -/
lemma fullRankContribution_le_leading
    {p m M r F : ℕ} (hp : 0 < p)
    (hF : F ≤ M.descFactorial r) :
    (m : ℝ) ^ r * F / (p : ℝ) ^ r ≤
      ((m : ℝ) * M / p) ^ r := by
  have hpR : (0 : ℝ) < (p : ℝ) ^ r := pow_pos (by exact_mod_cast hp) r
  have hFM : (F : ℝ) ≤ (M : ℝ) ^ r :=
    (Nat.cast_le.mpr hF).trans (by exact_mod_cast Nat.descFactorial_le_pow M r)
  rw [div_pow]
  apply div_le_div_of_nonneg_right _ hpR.le
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left hFM
    (pow_nonneg (show (0 : ℝ) ≤ (m : ℝ) by positivity) r)

/-- Explicit relative deficit of the full-rank term.  The two errors are the
collision error in replacing `(M)_r` by `M^r` and the proportion of incidence
patterns having lower rank. -/
lemma leading_sub_fullRankContribution_le
    {p m M r F L : ℕ} (hp : 0 < p) (hM : 0 < M)
    (hr0 : 0 < r) (hr : r ≤ M)
    (hpartition : F + L = M.descFactorial r) :
    ((m : ℝ) * M / p) ^ r - (m : ℝ) ^ r * F / (p : ℝ) ^ r ≤
      ((r : ℝ) ^ 2 / M + (L : ℝ) / (M : ℝ) ^ r) *
        ((m : ℝ) * M / p) ^ r := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hcount := fullRank_count_deficit hr hpartition
  have hpowM : (0 : ℝ) < (M : ℝ) ^ r := pow_pos hMR r
  have hpowp : (0 : ℝ) < (p : ℝ) ^ r := pow_pos hpR r
  have hpowm : (0 : ℝ) ≤ (m : ℝ) ^ r := pow_nonneg (Nat.cast_nonneg m) r
  have hident :
      ((r : ℝ) ^ 2 / M + (L : ℝ) / (M : ℝ) ^ r) * (M : ℝ) ^ r =
        (r : ℝ) ^ 2 * (M : ℝ) ^ (r - 1) + L := by
    have hsplit : (M : ℝ) ^ (r - 1) * M = (M : ℝ) ^ r := by
      exact pow_sub_one_mul (Nat.ne_of_gt hr0) (M : ℝ)
    field_simp
    nlinarith
  rw [div_pow]
  have hscaled := mul_le_mul_of_nonneg_left hcount hpowm
  have hscaled' := div_le_div_of_nonneg_right hscaled hpowp.le
  rw [← hident] at hscaled'
  calc
    ((m : ℝ) * M) ^ r / (p : ℝ) ^ r -
          (m : ℝ) ^ r * F / (p : ℝ) ^ r =
        (m : ℝ) ^ r * ((M : ℝ) ^ r - F) / (p : ℝ) ^ r := by ring
    _ ≤ (m : ℝ) ^ r *
          (((r : ℝ) ^ 2 / M + (L : ℝ) / (M : ℝ) ^ r) * (M : ℝ) ^ r) /
          (p : ℝ) ^ r := hscaled'
    _ = ((r : ℝ) ^ 2 / M + (L : ℝ) / (M : ℝ) ^ r) *
          (((m : ℝ) * M) ^ r / (p : ℝ) ^ r) := by ring

/-- An elementary two-sided combination lemma.  It is useful independently
of incidence matrices: a main contribution lying just below `theta` and a
small nonnegative error contribution give a relative approximation to
`theta`. -/
lemma abs_add_sub_le_of_contribution_bounds
    {theta full low epsFull epsLow : ℝ}
    (_htheta : 0 ≤ theta) (_hepsFull : 0 ≤ epsFull)
    (_hepsLow : 0 ≤ epsLow)
    (hfullUpper : full ≤ theta)
    (hfullLower : theta - full ≤ epsFull * theta)
    (hlow0 : 0 ≤ low) (hlowUpper : low ≤ epsLow * theta) :
    |full + low - theta| ≤ (epsFull + epsLow) * theta := by
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg _hepsLow _htheta]
  · nlinarith [mul_nonneg _hepsFull _htheta]

/-- Quantitative finite relative factorial-moment bound.  Here `F` and `L`
partition the full- and lower-rank incidence patterns, while `low` is the
actual lower-rank contribution to the factorial moment.  Thus the hypotheses
are exact count/fiber inputs, and the conclusion is the desired comparison
with `((m M)/p)^r`. -/
lemma abs_factorialMoment_sub_leading_le
    {p m M r F L : ℕ} {low epsLow : ℝ}
    (hp : 0 < p) (hM : 0 < M) (hr0 : 0 < r) (hr : r ≤ M)
    (hpartition : F + L = M.descFactorial r)
    (hlow0 : 0 ≤ low)
    (hlowUpper : low ≤ epsLow * (((m : ℝ) * M / p) ^ r))
    (hepsLow : 0 ≤ epsLow) :
    |((m : ℝ) ^ r * F / (p : ℝ) ^ r + low) -
        ((m : ℝ) * M / p) ^ r| ≤
      ((r : ℝ) ^ 2 / M + (L : ℝ) / (M : ℝ) ^ r + epsLow) *
        ((m : ℝ) * M / p) ^ r := by
  have hF : F ≤ M.descFactorial r := by omega
  have htheta : 0 ≤ ((m : ℝ) * M / p) ^ r := by positivity
  have hepsFull : 0 ≤ (r : ℝ) ^ 2 / M + (L : ℝ) / (M : ℝ) ^ r := by
    positivity
  have h := abs_add_sub_le_of_contribution_bounds htheta hepsFull hepsLow
    (fullRankContribution_le_leading hp hF)
    (leading_sub_fullRankContribution_le hp hM hr0 hr hpartition)
    hlow0 hlowUpper
  simpa only [add_assoc] using h

/-- Fully explicit rank-stratified version of the preceding estimate.  The
pointwise hypothesis on `C d` is precisely what follows from the low-rank
incidence count and the `3/4` hypercube loss. -/
lemma abs_rankStratifiedMoment_sub_leading_le
    {p k m M r F L : ℕ} {C : ℕ → ℕ}
    (hp : 0 < p) (hm : 0 < m) (hM : 0 < M) (hr0 : 0 < r) (hr : r ≤ M)
    (hpartition : F + L = M.descFactorial r)
    (hC : ∀ d ∈ Ico 1 r,
      (C d : ℝ) ≤ (m : ℝ) ^ r * (2 : ℝ) ^ (r * r) *
        ((3 : ℝ) / 4) ^ k * (((2 : ℝ) ^ k) ^ d)) :
    |((m : ℝ) ^ r * F / (p : ℝ) ^ r + lowRankContribution p r C) -
        ((m : ℝ) * M / p) ^ r| ≤
      ((r : ℝ) ^ 2 / M + (L : ℝ) / (M : ℝ) ^ r +
          incidenceLowRankEnvelope p k r m /
            (((m : ℝ) * M / p) ^ r)) *
        ((m : ℝ) * M / p) ^ r := by
  let theta : ℝ := ((m : ℝ) * M / p) ^ r
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have htheta : 0 < theta := by
    dsimp [theta]
    positivity
  have henv0 : 0 ≤ incidenceLowRankEnvelope p k r m := by
    rw [incidenceLowRankEnvelope]
    positivity
  have hlow := lowRankContribution_le_incidenceEnvelope hp hC
  have hlow' : lowRankContribution p r C ≤
      (incidenceLowRankEnvelope p k r m / theta) * theta := by
    rw [div_mul_cancel₀ _ htheta.ne']
    exact hlow
  simpa only [theta] using
    (abs_factorialMoment_sub_leading_le hp hM hr0 hr hpartition
      (lowRankContribution_nonneg p r C) hlow'
      (div_nonneg henv0 htheta.le))

/-- The same estimate with the number of lower-rank patterns replaced by its
explicit trivial incidence bound. -/
lemma abs_rankStratifiedMoment_sub_leading_le_explicit
    {p k m M r F L : ℕ} {C T : ℕ → ℕ}
    (hp : 0 < p) (hm : 0 < m) (hM : 0 < M) (hr0 : 0 < r) (hr : r ≤ M)
    (hpartition : F + L = M.descFactorial r)
    (hL : L = lowerRankPatternCount r T)
    (hT : ∀ d ∈ Ico 1 r,
      T d ≤ 2 ^ (r * r) * (2 ^ k) ^ d)
    (hC : ∀ d ∈ Ico 1 r,
      (C d : ℝ) ≤ (m : ℝ) ^ r * (2 : ℝ) ^ (r * r) *
        ((3 : ℝ) / 4) ^ k * (((2 : ℝ) ^ k) ^ d)) :
    |((m : ℝ) ^ r * F / (p : ℝ) ^ r + lowRankContribution p r C) -
        ((m : ℝ) * M / p) ^ r| ≤
      ((r : ℝ) ^ 2 / M +
          ((r * 2 ^ (r * r) * (2 ^ k) ^ (r - 1) : ℕ) : ℝ) /
            (M : ℝ) ^ r +
          incidenceLowRankEnvelope p k r m /
            (((m : ℝ) * M / p) ^ r)) *
        ((m : ℝ) * M / p) ^ r := by
  have hbase := abs_rankStratifiedMoment_sub_leading_le
    hp hm hM hr0 hr hpartition hC
  have hLbound : L ≤ r * 2 ^ (r * r) * (2 ^ k) ^ (r - 1) := by
    rw [hL]
    exact lowerRankPatternCount_le_last hT
  have hden : 0 ≤ (M : ℝ) ^ r := by positivity
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  gcongr

end Erdos543
