/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.Parameters
import ErdosProblems.Erdos63.AvoidanceDeep

/-!
# Source-scale arithmetic for Liu--Montgomery Lemmas 3.5 and 3.7

This file is graph-free.  It records a literal small/large split of the form
used in the source proof.  The small/large cutoff is `log(N)^(1/10)`, the
largest failed set has order `log(N)^(1/5)`, the large and small sample
multiplicities are respectively `D^2` and `r^2`, and the trace of an
`r`-set on the deleted set has size at most `r*d`.

The main estimate is uniform in `d`: once `N` is large, every `d ≤ N` and
every finite deleted set below the source envelope satisfy the two
pigeonhole bounds.  When `d/1024` is larger than `D`, there cannot be a
failed set at all; the theorem records this as a separate alternative.
-/

open Filter Finset Set
open scoped BigOperators

namespace Erdos63.SourceLemma35Numerics

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The source cutoff `ceil(log(N)^(1/10))`. -/
noncomputable def cutoff (N : ℕ) : ℕ :=
  ⌈Real.log (N : ℝ) ^ ((1 : ℝ) / 10)⌉₊

/-- A convenient polylogarithmic upper size, equal to the square of the
source cutoff and hence of order `log(N)^(1/5)`. -/
noncomputable def maxFailedSize (N : ℕ) : ℕ := cutoff N ^ 2

/-- The lower size of a failed set.  The maximum with one removes all
small-`d` degeneracies without changing the eventual source scale. -/
def minFailedSize (d : ℕ) : ℕ := max 1 (d / 1024)

/-- The source large-set multiplicity. -/
noncomputable def qLarge (N : ℕ) : ℕ := maxFailedSize N ^ 2

/-- The source small-set multiplicity. -/
def qSmall (r : ℕ) : ℕ := r ^ 2

/-- The source upper bound on the trace in the deleted set. -/
def blockedBudget (d r : ℕ) : ℕ := r * d

/-- The quasi-polylogarithmic envelope allowed for the common deleted set. -/
noncomputable def deletionCap (N : ℕ) : ℕ :=
  ⌊Real.exp (Real.log (Real.log (N : ℝ)) ^ 2)⌋₊

/-- The number of failed vertices allowed by the source indexing argument. -/
noncomputable def indexCard (N : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ ((1 : ℝ) / 8)⌋₊

theorem qSmall_pos {r : ℕ} (hr : 0 < r) : 0 < qSmall r := by
  simp [qSmall, hr]

theorem deletionCap_cast_le (N : ℕ) :
    (deletionCap N : ℝ) ≤
      Real.exp (Real.log (Real.log (N : ℝ)) ^ 2) := by
  exact Nat.floor_le (Real.exp_pos _).le

/-- The bounded-label theorem from `AvoidanceDeep`, specialized to the
source contact budget. -/
theorem card_boundedSubsets_source {V : Type*} (U : Finset V) (d r : ℕ) :
    (boundedSubsets U (blockedBudget d r)).card ≤
      (blockedBudget d r + 1) *
        (max 1 U.card) ^ (blockedBudget d r) := by
  exact card_boundedSubsets_le_mul_pow U (blockedBudget d r)

/-! ## Elementary uniform bounds inside the small range -/

theorem degree_le_of_small_range {d r : ℕ}
    (hr : minFailedSize d ≤ r) : d ≤ 1024 * (r + 1) := by
  have hdiv : d / 1024 ≤ r := (le_max_right 1 (d / 1024)).trans hr
  omega

theorem blockedBudget_le_of_small_range {N d r : ℕ}
    (hr : minFailedSize d ≤ r) (hrcut : r < cutoff N) :
    blockedBudget d r ≤ 2048 * cutoff N ^ 2 := by
  have hd := degree_le_of_small_range hr
  have hrle : r ≤ cutoff N := Nat.le_of_lt hrcut
  have hminpos : 0 < minFailedSize d := by simp [minFailedSize]
  have hcutpos : 0 < cutoff N := (hminpos.trans_le hr).trans hrcut
  dsimp [blockedBudget]
  calc
    r * d ≤ cutoff N * (1024 * (r + 1)) := Nat.mul_le_mul hrle hd
    _ ≤ cutoff N * (1024 * (cutoff N + 1)) := by gcongr
    _ ≤ 2048 * cutoff N ^ 2 := by
      nlinarith

/-! ## A common envelope for both pigeonhole counts -/

/-- A real envelope for the complete small-size sum.  The factor
`2048 * cutoff^2` bounds every contact trace in the small range. -/
noncomputable def sampleEnvelope (N : ℕ) : ℝ :=
  (cutoff N : ℝ) ^ 4 * ((2048 * cutoff N ^ 2 + 1 : ℕ) : ℝ) *
    Real.exp (((2048 * cutoff N ^ 2 : ℕ) : ℝ) *
      Real.log (Real.log (N : ℝ)) ^ 2)

/-- The source large contribution `qLarge * D` is bounded by the same
envelope used for the more expensive small-set trace count. -/
theorem largeSample_cast_le_envelope {N : ℕ} (hcut : 0 < cutoff N) :
    ((qLarge N * maxFailedSize N : ℕ) : ℝ) ≤ sampleEnvelope N := by
  have hcutR : (1 : ℝ) ≤ cutoff N := by exact_mod_cast hcut
  have hexpOne : (1 : ℝ) ≤
      Real.exp (((2048 * cutoff N ^ 2 : ℕ) : ℝ) *
        Real.log (Real.log (N : ℝ)) ^ 2) := by
    rw [Real.one_le_exp_iff]
    positivity
  rw [qLarge, maxFailedSize, sampleEnvelope]
  push_cast
  have hfactor : (cutoff N : ℝ) ^ 2 ≤
      (2048 : ℝ) * (cutoff N : ℝ) ^ 2 + 1 := by
    nlinarith [sq_nonneg (cutoff N : ℝ)]
  calc
    ((cutoff N : ℝ) ^ 2) ^ 2 * (cutoff N : ℝ) ^ 2
        = (cutoff N : ℝ) ^ 4 * (cutoff N : ℝ) ^ 2 := by ring
    _ ≤ (cutoff N : ℝ) ^ 4 *
        ((2048 : ℝ) * (cutoff N : ℝ) ^ 2 + 1) := by gcongr
    _ ≤ (cutoff N : ℝ) ^ 4 *
        ((2048 : ℝ) * (cutoff N : ℝ) ^ 2 + 1) *
          Real.exp (((2048 : ℝ) * (cutoff N : ℝ) ^ 2) *
            Real.log (Real.log (N : ℝ)) ^ 2) := by
      apply le_mul_of_one_le_right (by positivity)
      simpa using hexpOne

/-- Every actual small-size label sum is at most `sampleEnvelope`.  This is
the finite source-faithful use of the bounded-subset count: it counts only
traces of size at most `r*d`, rather than all subsets of the deleted set. -/
theorem smallSample_cast_le_envelope {V : Type*} (U : Finset V) {N d : ℕ}
    (hU : U.card ≤ deletionCap N) :
    ((∑ r ∈ Finset.Ico (minFailedSize d) (cutoff N),
        r * ((boundedSubsets U (blockedBudget d r)).card * qSmall r) : ℕ) : ℝ)
      ≤ sampleEnvelope N := by
  let Cmax : ℕ := 2048 * cutoff N ^ 2
  let A : ℝ := Real.log (Real.log (N : ℝ)) ^ 2
  let term : ℝ := (cutoff N : ℝ) ^ 3 * (Cmax + 1 : ℕ) *
    Real.exp ((Cmax : ℝ) * A)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcap : (deletionCap N : ℝ) ≤ Real.exp A := by
    simpa [A] using deletionCap_cast_le N
  have hUreal : (U.card : ℝ) ≤ Real.exp A := by
    exact (by exact_mod_cast hU : (U.card : ℝ) ≤ deletionCap N) |>.trans hcap
  have honeExp : (1 : ℝ) ≤ Real.exp A := by
    simpa [Real.one_le_exp_iff] using hA
  have hbase : ((max 1 U.card : ℕ) : ℝ) ≤ Real.exp A := by
    simp only [Nat.cast_max, Nat.cast_one]
    exact max_le honeExp hUreal
  have hterm : ∀ r ∈ Finset.Ico (minFailedSize d) (cutoff N),
      ((r * ((boundedSubsets U (blockedBudget d r)).card * qSmall r) : ℕ) : ℝ)
        ≤ term := by
    intro r hr
    have hrmin : minFailedSize d ≤ r := (Finset.mem_Ico.1 hr).1
    have hrcut : r < cutoff N := (Finset.mem_Ico.1 hr).2
    have hrle : r ≤ cutoff N := Nat.le_of_lt hrcut
    have hC : blockedBudget d r ≤ Cmax := by
      simpa [Cmax] using blockedBudget_le_of_small_range hrmin hrcut
    have hlabelNat := card_boundedSubsets_source U d r
    have hlabel : ((boundedSubsets U (blockedBudget d r)).card : ℝ) ≤
        ((blockedBudget d r + 1 : ℕ) : ℝ) *
          (((max 1 U.card : ℕ) : ℝ) ^ blockedBudget d r) := by
      exact_mod_cast hlabelNat
    have hpowBase : (((max 1 U.card : ℕ) : ℝ) ^ blockedBudget d r) ≤
        (Real.exp A) ^ blockedBudget d r := by
      exact pow_le_pow_left₀ (by positivity) hbase _
    have hpowExponent : (Real.exp A) ^ blockedBudget d r ≤
        (Real.exp A) ^ Cmax := by
      exact pow_le_pow_right₀ honeExp hC
    have hpowExp : (Real.exp A) ^ Cmax =
        Real.exp ((Cmax : ℝ) * A) := by
      rw [← Real.exp_nat_mul]
    have hlabelEnvelope : ((boundedSubsets U (blockedBudget d r)).card : ℝ) ≤
        ((Cmax + 1 : ℕ) : ℝ) * Real.exp ((Cmax : ℝ) * A) := by
      calc
        ((boundedSubsets U (blockedBudget d r)).card : ℝ)
            ≤ ((blockedBudget d r + 1 : ℕ) : ℝ) *
                (((max 1 U.card : ℕ) : ℝ) ^ blockedBudget d r) := hlabel
        _ ≤ ((Cmax + 1 : ℕ) : ℝ) * (Real.exp A) ^ Cmax := by
          gcongr
          exact hpowBase.trans hpowExponent
        _ = ((Cmax + 1 : ℕ) : ℝ) * Real.exp ((Cmax : ℝ) * A) := by
          rw [hpowExp]
    dsimp [qSmall, term]
    push_cast
    calc
      (r : ℝ) *
          (((boundedSubsets U (blockedBudget d r)).card : ℝ) * (r : ℝ) ^ 2)
          = (r : ℝ) ^ 3 *
              ((boundedSubsets U (blockedBudget d r)).card : ℝ) := by ring
      _ ≤ (cutoff N : ℝ) ^ 3 *
          (((Cmax : ℝ) + 1) * Real.exp ((Cmax : ℝ) * A)) := by
        gcongr
        simpa using hlabelEnvelope
      _ = (cutoff N : ℝ) ^ 3 * ((Cmax : ℝ) + 1) *
          Real.exp ((Cmax : ℝ) * A) := by ring
  have hcard : (Finset.Ico (minFailedSize d) (cutoff N)).card ≤ cutoff N := by
    simp
  calc
    ((∑ r ∈ Finset.Ico (minFailedSize d) (cutoff N),
        r * ((boundedSubsets U (blockedBudget d r)).card * qSmall r) : ℕ) : ℝ)
        = ∑ r ∈ Finset.Ico (minFailedSize d) (cutoff N),
            ((r * ((boundedSubsets U (blockedBudget d r)).card * qSmall r) : ℕ) : ℝ) := by
          push_cast
          rfl
    _ ≤ ∑ _r ∈ Finset.Ico (minFailedSize d) (cutoff N), term := by
      exact Finset.sum_le_sum fun r hr ↦ hterm r hr
    _ = ((Finset.Ico (minFailedSize d) (cutoff N)).card : ℝ) * term := by simp
    _ ≤ (cutoff N : ℝ) * term := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = sampleEnvelope N := by
      simp only [sampleEnvelope, term, Cmax, A]
      push_cast
      ring

/-! ## The envelope is sub-polynomial -/

theorem eventually_cutoff_cast_le_two_rpow :
    ∀ᶠ N : ℕ in atTop,
      (cutoff N : ℝ) ≤
        2 * Real.log (N : ℝ) ^ ((1 : ℝ) / 10) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hlog
  filter_upwards [hpow.eventually (eventually_ge_atTop (1 : ℝ)),
      hlog.eventually (eventually_ge_atTop (1 : ℝ))] with N hN hlogN
  have hceil : (cutoff N : ℝ) <
      Real.log (N : ℝ) ^ ((1 : ℝ) / 10) + 1 := by
    exact Nat.ceil_lt_add_one
      (Real.rpow_nonneg (zero_le_one.trans hlogN) _)
  linarith

theorem eventually_log_log_sq_le_log_rpow_tenth :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Real.log (N : ℝ)) ^ 2 ≤
        Real.log (N : ℝ) ^ ((1 : ℝ) / 10) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound :=
    (isLittleO_log_rpow_rpow_atTop 2
      (by norm_num : (0 : ℝ) < 1 / 10)).bound
        (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hlog.eventually hbound,
      hlog.eventually (eventually_ge_atTop (0 : ℝ))] with N hN hNnonneg
  rw [Real.rpow_two] at hN
  rw [Real.norm_eq_abs] at hN
  calc
    Real.log (Real.log (N : ℝ)) ^ (2 : ℕ)
        ≤ |Real.log (Real.log (N : ℝ)) ^ (2 : ℕ)| := le_abs_self _
    _ ≤ 1 * ‖Real.log (N : ℝ) ^ ((1 : ℝ) / 10)‖ := hN
    _ = Real.log (N : ℝ) ^ ((1 : ℝ) / 10) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hNnonneg _)]
      simp

private theorem envelope_exponent_le
    {N : ℕ}
    (hlogOne : 1 ≤ Real.log (N : ℝ))
    (hcut : (cutoff N : ℝ) ≤
      2 * Real.log (N : ℝ) ^ ((1 : ℝ) / 10))
    (hloglog : Real.log (Real.log (N : ℝ)) ^ 2 ≤
      Real.log (N : ℝ) ^ ((1 : ℝ) / 10))
    (hroot : (524288 : ℝ) ≤
      Real.log (N : ℝ) ^ ((1 : ℝ) / 2)) :
    (((2048 * cutoff N ^ 2 : ℕ) : ℝ) *
        Real.log (Real.log (N : ℝ)) ^ 2) ≤
      Real.log (N : ℝ) / 64 := by
  let t : ℝ := Real.log (N : ℝ)
  have ht : (1 : ℝ) ≤ t := hlogOne
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hpowTwo : (t ^ ((1 : ℝ) / 10)) ^ 2 =
      t ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]
    norm_num
  have hpowAdd : t ^ ((1 : ℝ) / 5) * t ^ ((1 : ℝ) / 10) =
      t ^ ((3 : ℝ) / 10) := by
    rw [← Real.rpow_add htpos]
    norm_num
  have hcutSq : (cutoff N : ℝ) ^ 2 ≤
      4 * t ^ ((1 : ℝ) / 5) := by
    calc
      (cutoff N : ℝ) ^ 2 ≤
          (2 * t ^ ((1 : ℝ) / 10)) ^ 2 := by
        gcongr
      _ = 4 * t ^ ((1 : ℝ) / 5) := by
        rw [mul_pow, hpowTwo]
        ring
  have hexponent : (((2048 * cutoff N ^ 2 : ℕ) : ℝ) *
        Real.log (Real.log (N : ℝ)) ^ 2) ≤
      8192 * t ^ ((3 : ℝ) / 10) := by
    push_cast
    calc
      2048 * (cutoff N : ℝ) ^ 2 *
          Real.log (Real.log (N : ℝ)) ^ 2
          ≤ 2048 * (4 * t ^ ((1 : ℝ) / 5)) *
              t ^ ((1 : ℝ) / 10) := by gcongr
      _ = 8192 * t ^ ((3 : ℝ) / 10) := by
        calc
          2048 * (4 * t ^ ((1 : ℝ) / 5)) * t ^ ((1 : ℝ) / 10) =
              8192 * (t ^ ((1 : ℝ) / 5) * t ^ ((1 : ℝ) / 10)) := by ring
          _ = 8192 * t ^ ((3 : ℝ) / 10) := by rw [hpowAdd]
  have hthreeTenths : t ^ ((3 : ℝ) / 10) ≤ t ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
  have hrootSq : (t ^ ((1 : ℝ) / 2)) ^ 2 = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]
    norm_num
  have hfinal : 8192 * t ^ ((3 : ℝ) / 10) ≤ t / 64 := by
    have hy0 : 0 ≤ t ^ ((1 : ℝ) / 2) := Real.rpow_nonneg ht0 _
    calc
      8192 * t ^ ((3 : ℝ) / 10)
          ≤ 8192 * t ^ ((1 : ℝ) / 2) := by gcongr
      _ ≤ t / 64 := by nlinarith
  exact hexponent.trans hfinal

private theorem envelope_prefactor_le
    {N : ℕ}
    (hlogOne : 1 ≤ Real.log (N : ℝ))
    (hcut : (cutoff N : ℝ) ≤
      2 * Real.log (N : ℝ) ^ ((1 : ℝ) / 10)) :
    (cutoff N : ℝ) ^ 4 * ((2048 * cutoff N ^ 2 + 1 : ℕ) : ℝ) ≤
      131088 * Real.log (N : ℝ) ^ 6 := by
  let t : ℝ := Real.log (N : ℝ)
  have ht : (1 : ℝ) ≤ t := hlogOne
  have hsmallPow : t ^ ((1 : ℝ) / 10) ≤ t := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (1 : ℝ) / 10 ≤ 1))
  have hcutLinear : (cutoff N : ℝ) ≤ 2 * t := hcut.trans (by gcongr)
  have hcutFour : (cutoff N : ℝ) ^ 4 ≤ 16 * t ^ 4 := by
    calc
      (cutoff N : ℝ) ^ 4 ≤ (2 * t) ^ 4 := by gcongr
      _ = 16 * t ^ 4 := by ring
  have hfactor : ((2048 * cutoff N ^ 2 + 1 : ℕ) : ℝ) ≤ 8193 * t ^ 2 := by
    push_cast
    have htSq : (1 : ℝ) ≤ t ^ 2 := by nlinarith
    nlinarith [sq_nonneg ((cutoff N : ℝ) - 2 * t)]
  calc
    (cutoff N : ℝ) ^ 4 * ((2048 * cutoff N ^ 2 + 1 : ℕ) : ℝ)
        ≤ (16 * t ^ 4) * (8193 * t ^ 2) := by gcongr
    _ = 131088 * t ^ 6 := by ring

theorem eventually_four_mul_sampleEnvelope_le_indexRoot :
    ∀ᶠ N : ℕ in atTop,
      4 * sampleEnvelope N ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hroot : Tendsto
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ ((1 : ℝ) / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hlog
  have hpolyReal :=
    (isLittleO_pow_exp_pos_mul_atTop 6
      (by norm_num : (0 : ℝ) < 1 / 64)).bound
        (show (0 : ℝ) < 1 / 524352 by norm_num)
  have hpoly : ∀ᶠ N : ℕ in atTop,
      4 * 131088 * Real.log (N : ℝ) ^ 6 ≤
        Real.exp (Real.log (N : ℝ) / 64) := by
    filter_upwards [hlog.eventually hpolyReal,
        hlog.eventually (eventually_ge_atTop (0 : ℝ))] with N hN ht
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht 6),
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hN
    have hN' : Real.log (N : ℝ) ^ 6 ≤
        (1 / 524352 : ℝ) * Real.exp (Real.log (N : ℝ) / 64) := by
      simpa [div_eq_mul_inv, mul_comm] using hN
    calc
      4 * 131088 * Real.log (N : ℝ) ^ 6 =
          524352 * Real.log (N : ℝ) ^ 6 := by ring
      _ ≤ 524352 * ((1 / 524352 : ℝ) *
          Real.exp (Real.log (N : ℝ) / 64)) := by gcongr
      _ = Real.exp (Real.log (N : ℝ) / 64) := by ring
  filter_upwards [eventually_cutoff_cast_le_two_rpow,
      eventually_log_log_sq_le_log_rpow_tenth,
      hlog.eventually (eventually_ge_atTop (1 : ℝ)),
      hroot.eventually (eventually_ge_atTop (524288 : ℝ)), hpoly,
      eventually_ge_atTop (1 : ℕ)] with N hcut hloglog hlogOne hrootN hpolyN hNpos
  have hexponent := envelope_exponent_le hlogOne hcut hloglog hrootN
  have hprefactor := envelope_prefactor_le hlogOne hcut
  have hfourPrefactor :
      4 * ((cutoff N : ℝ) ^ 4 *
        ((2048 * cutoff N ^ 2 + 1 : ℕ) : ℝ)) ≤
          Real.exp (Real.log (N : ℝ) / 64) := by
    calc
      4 * ((cutoff N : ℝ) ^ 4 *
          ((2048 * cutoff N ^ 2 + 1 : ℕ) : ℝ))
          ≤ 4 * (131088 * Real.log (N : ℝ) ^ 6) := by gcongr
      _ = 4 * 131088 * Real.log (N : ℝ) ^ 6 := by ring
      _ ≤ Real.exp (Real.log (N : ℝ) / 64) := hpolyN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  calc
    4 * sampleEnvelope N =
        (4 * ((cutoff N : ℝ) ^ 4 *
          ((2048 * cutoff N ^ 2 + 1 : ℕ) : ℝ))) *
            Real.exp (((2048 * cutoff N ^ 2 : ℕ) : ℝ) *
              Real.log (Real.log (N : ℝ)) ^ 2) := by
      simp only [sampleEnvelope]
      ring
    _ ≤ Real.exp (Real.log (N : ℝ) / 64) *
          Real.exp (Real.log (N : ℝ) / 64) := by gcongr
    _ = Real.exp (Real.log (N : ℝ) / 32) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Real.log (N : ℝ) / 8) := by
      gcongr
      have := zero_le_one.trans hlogOne
      linarith
    _ = (N : ℝ) ^ ((1 : ℝ) / 8) := by
      rw [Real.rpow_def_of_pos hNreal]
      congr 1
      ring

/-! ## Floor-safe natural pigeonhole bounds -/

private theorem le_index_half_of_cast_le_envelope
    {N x : ℕ}
    (hroot : 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 8))
    (henvelope : 4 * sampleEnvelope N ≤
      (N : ℝ) ^ ((1 : ℝ) / 8))
    (hx : (x : ℝ) ≤ sampleEnvelope N) :
    x ≤ (indexCard N + 1) / 2 := by
  have hfour : ((4 * x : ℕ) : ℝ) ≤
      (N : ℝ) ^ ((1 : ℝ) / 8) := by
    calc
      ((4 * x : ℕ) : ℝ) = 4 * (x : ℝ) := by norm_num
      _ ≤ 4 * sampleEnvelope N := by gcongr
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := henvelope
  have hfloor : (N : ℝ) ^ ((1 : ℝ) / 8) / 2 ≤
      (indexCard N : ℝ) := by
    simpa [indexCard] using Parameters.half_le_natFloor hroot
  have htwoReal : ((2 * x : ℕ) : ℝ) ≤ (indexCard N : ℝ) := by
    calc
      ((2 * x : ℕ) : ℝ) = ((4 * x : ℕ) : ℝ) / 2 := by
        push_cast
        ring
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 8) / 2 := by gcongr
      _ ≤ (indexCard N : ℝ) := hfloor
  have htwo : 2 * x ≤ indexCard N := by exact_mod_cast htwoReal
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
  omega

/-- Pointwise source pigeonhole arithmetic.  The first conclusion is the
large-family sample bound with multiplicity `D^2`; the second is the exact
bounded-trace sum with small multiplicity `r^2`. -/
theorem source_pigeonhole_bounds_of_envelope
    {N d : ℕ} {V : Type*} (U : Finset V)
    (hcut : 0 < cutoff N)
    (hroot : 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 8))
    (henvelope : 4 * sampleEnvelope N ≤
      (N : ℝ) ^ ((1 : ℝ) / 8))
    (hU : U.card ≤ deletionCap N) :
    qLarge N * maxFailedSize N ≤ (indexCard N + 1) / 2 ∧
      ∑ r ∈ Finset.Ico (minFailedSize d) (cutoff N),
        r * ((boundedSubsets U (blockedBudget d r)).card * qSmall r) ≤
          (indexCard N + 1) / 2 := by
  constructor
  · apply le_index_half_of_cast_le_envelope hroot henvelope
    exact largeSample_cast_le_envelope hcut
  · apply le_index_half_of_cast_le_envelope hroot henvelope
    exact smallSample_cast_le_envelope U hU

/-- If the lower failed-set scale has passed the polylogarithmic maximum,
there is no admissible failed cardinality.  This is the branch which makes
the final uniform statement meaningful even when `d` is close to `N`. -/
theorem no_failed_cardinality_of_max_lt_min {N d s : ℕ}
    (hgap : maxFailedSize N < minFailedSize d)
    (hmin : minFailedSize d ≤ s) (hmax : s ≤ maxFailedSize N) : False := by
  omega

/-- The three ambient estimates required by the pointwise theorem hold on
one tail of the natural numbers. -/
theorem eventually_source_ambient_bounds :
    ∀ᶠ N : ℕ in atTop,
      0 < cutoff N ∧
      2 ≤ (N : ℝ) ^ ((1 : ℝ) / 8) ∧
      4 * sampleEnvelope N ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
  have hroot : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ ((1 : ℝ) / 8))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ),
      hroot.eventually (eventually_ge_atTop (2 : ℝ)),
      eventually_four_mul_sampleEnvelope_le_indexRoot] with N hN hrootN henv
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hcut : 0 < cutoff N := by
    apply Nat.ceil_pos.mpr
    exact Real.rpow_pos_of_pos hlogpos _
  exact ⟨hcut, hrootN, henv⟩

/-- Eventual theorem in the form used by the source argument.  It is uniform
in every `d ≤ N` and every deleted set below `deletionCap N`. -/
theorem eventually_source_pigeonhole_bounds {V : Type*} :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, d ≤ N → ∀ U : Finset V,
      U.card ≤ deletionCap N →
      qLarge N * maxFailedSize N ≤ (indexCard N + 1) / 2 ∧
        ∑ r ∈ Finset.Ico (minFailedSize d) (cutoff N),
          r * ((boundedSubsets U (blockedBudget d r)).card * qSmall r) ≤
            (indexCard N + 1) / 2 := by
  filter_upwards [eventually_source_ambient_bounds] with N hN
  intro d _hd U hU
  exact source_pigeonhole_bounds_of_envelope U hN.1 hN.2.1 hN.2.2 hU

/-- Explicit-threshold version of `eventually_source_pigeonhole_bounds`. -/
theorem exists_source_pigeonhole_threshold {V : Type*} :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ d : ℕ, d ≤ N → ∀ U : Finset V,
      U.card ≤ deletionCap N →
      qLarge N * maxFailedSize N ≤ (indexCard N + 1) / 2 ∧
        ∑ r ∈ Finset.Ico (minFailedSize d) (cutoff N),
          r * ((boundedSubsets U (blockedBudget d r)).card * qSmall r) ≤
            (indexCard N + 1) / 2 := by
  simpa only [eventually_atTop] using
    (eventually_source_pigeonhole_bounds (V := V))

end Erdos63.SourceLemma35Numerics
