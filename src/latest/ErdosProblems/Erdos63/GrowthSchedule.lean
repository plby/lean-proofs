/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.AdjusterJoin
import ErdosProblems.Erdos63.AdjusterBase
import ErdosProblems.Erdos63.Claim46Growth
import ErdosProblems.Erdos63.Lemma311
import ErdosProblems.Erdos63.Lemma315
import ErdosProblems.Erdos63.Parameters

/-!
# Concrete growth schedules for the Liu--Montgomery expander

This file removes the abstract growth schedules from the final assembly.  At
the Komlós--Szemerédi parameters

* `epsilon = 1 / 1024`, and
* `kappa = (1 / 64) * d`,

the expansion available from a set of order `s` is at least
`s / (9216 * log(N)^2)`.  Half of this quantity is reserved for new vertices
and half for blocked contacts.  The resulting natural-valued recurrence
doubles in a block of `O(log(N)^2)` rounds, and consequently reaches more
than half of an `N`-vertex graph in `O(log(N)^3)` rounds.

The last two theorems are the limited-contact versions needed in the actual
Liu--Montgomery argument.  They pay for `X` and `Y` globally, but pay for the
possibly much larger set `Z` only through the vertices of `Z` which the ball
actually meets.  Thus they do not charge a retained `D`-vertex expansion as
part of the workspace at every round.
-/

open Finset Set SimpleGraph
open scoped BigOperators SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {V : Type u} {G : SimpleGraph V}

/-! ## A uniform lower bound for the expansion profile -/

/-- On the whole range relevant to an `N`-vertex graph, the exact
Liu--Montgomery profile is bounded below by a fixed multiple of
`1 / log(N)^2`.  The constant `9216 = 1024 * 3^2` comes from
`15s / (d/64) = 960s/d <= N^3` when `N >= 32`, `d >= 1`, and `s <= N`. -/
theorem lm_expansion_profile_lower
    {N d s : ℕ} (hN : 32 ≤ N) (hd : 1 ≤ d)
    (hcutoff : (d : ℝ) / 128 ≤ (s : ℝ)) (hsN : s ≤ N) :
    (s : ℝ) / (9216 * Real.log (N : ℝ) ^ 2) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hd)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hk : ((1 / 64 : ℝ) * (d : ℝ)) / 5 ≤ (s : ℝ) := by
    norm_num at hcutoff ⊢
    linarith
  rw [expansionEpsilon_of_le hk]
  have harg :
      15 * (s : ℝ) / ((1 / 64 : ℝ) * (d : ℝ)) =
        960 * (s : ℝ) / (d : ℝ) := by
    field_simp [ne_of_gt hdpos]
    <;> ring
  rw [harg]
  have hratioOne : (1 : ℝ) < 960 * (s : ℝ) / (d : ℝ) := by
    rw [lt_div_iff₀ hdpos]
    nlinarith
  have hsNreal : (s : ℝ) ≤ (N : ℝ) := by exact_mod_cast hsN
  have hdOne : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hratioN : 960 * (s : ℝ) / (d : ℝ) ≤ 960 * (N : ℝ) := by
    calc
      960 * (s : ℝ) / (d : ℝ)
          ≤ 960 * (N : ℝ) / (d : ℝ) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsNreal (by norm_num)) hdpos.le
      _ ≤ 960 * (N : ℝ) := div_le_self (by positivity) hdOne
  have hNsquare : (960 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have hNreal : (32 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [sq_nonneg ((N : ℝ) - 32)]
  have hratioCube :
      960 * (s : ℝ) / (d : ℝ) ≤ (N : ℝ) ^ 3 := by
    calc
      960 * (s : ℝ) / (d : ℝ) ≤ 960 * (N : ℝ) := hratioN
      _ ≤ (N : ℝ) * (N : ℝ) ^ 2 :=
        by
          simpa [mul_comm] using
            (mul_le_mul_of_nonneg_right hNsquare hNpos.le)
      _ = (N : ℝ) ^ 3 := by ring
  have hlogUpper :
      Real.log (960 * (s : ℝ) / (d : ℝ)) ≤
        3 * Real.log (N : ℝ) := by
    calc
      Real.log (960 * (s : ℝ) / (d : ℝ))
          ≤ Real.log ((N : ℝ) ^ 3) :=
            Real.log_le_log (by positivity) hratioCube
      _ = 3 * Real.log (N : ℝ) := by rw [Real.log_pow]; norm_num
  have hlogNonneg :
      0 ≤ Real.log (960 * (s : ℝ) / (d : ℝ)) :=
    (Real.log_pos hratioOne).le
  have hsq :
      Real.log (960 * (s : ℝ) / (d : ℝ)) ^ 2 ≤
        (3 * Real.log (N : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hlogNonneg hlogUpper 2
  have hden :
      1024 * Real.log (960 * (s : ℝ) / (d : ℝ)) ^ 2 ≤
        9216 * Real.log (N : ℝ) ^ 2 := by
    nlinarith
  calc
    (s : ℝ) / (9216 * Real.log (N : ℝ) ^ 2)
        ≤ (s : ℝ) /
            (1024 * Real.log (960 * (s : ℝ) / (d : ℝ)) ^ 2) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg s)
        (by
          have hlogpos := Real.log_pos hratioOne
          positivity)
        hden
    _ = ((1 / 1024 : ℝ) /
          Real.log (960 * (s : ℝ) / (d : ℝ)) ^ 2) * (s : ℝ) := by
      ring

/-! ## The natural multiplicative curve -/

/-- A natural denominator safely above `9216 * log(N)^2`. -/
noncomputable def lmGrowthDenominator (N : ℕ) : ℕ :=
  ⌈9216 * Real.log (N : ℝ) ^ 2⌉₊

/-- Twice `lmGrowthDenominator`; one copy is reserved for growth and one for
blocked contacts. -/
noncomputable def lmGrowthDivisor (N : ℕ) : ℕ :=
  2 * lmGrowthDenominator N

/-- The new vertices requested at one multiplicative-growth step. -/
noncomputable def lmGrowthGain (N s : ℕ) : ℕ :=
  s / lmGrowthDivisor N

/-- The concrete lower curve used by both schedule interfaces. -/
noncomputable def lmGrowthCurve (N D : ℕ) : ℕ → ℕ
  | 0 => D
  | i + 1 => lmGrowthCurve N D i + lmGrowthGain N (lmGrowthCurve N D i)

/-- The number of rounds: `2 * divisor` rounds for every binary doubling. -/
noncomputable def lmGrowthRounds (N : ℕ) : ℕ :=
  2 * lmGrowthDivisor N * (Nat.log 2 N + 1)

theorem lmGrowthDenominator_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < lmGrowthDenominator N := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (by norm_num) (sq_pos_of_pos <|
    Real.log_pos (by exact_mod_cast (by omega : 1 < N)))

theorem lmGrowthDivisor_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < lmGrowthDivisor N := by
  exact mul_pos (by omega) (lmGrowthDenominator_pos hN)

theorem lmGrowthDenominator_lower (N : ℕ) :
    9216 * Real.log (N : ℝ) ^ 2 ≤ (lmGrowthDenominator N : ℝ) := by
  exact Nat.le_ceil _

theorem lmGrowthGain_mono (N : ℕ) : Monotone (lmGrowthGain N) := by
  intro a b hab
  exact Nat.div_le_div_right hab

@[simp] theorem lmGrowthCurve_zero (N D : ℕ) :
    lmGrowthCurve N D 0 = D := rfl

@[simp] theorem lmGrowthCurve_succ (N D i : ℕ) :
    lmGrowthCurve N D (i + 1) =
      lmGrowthCurve N D i + lmGrowthGain N (lmGrowthCurve N D i) := rfl

theorem lmGrowthCurve_mono (N D : ℕ) : Monotone (lmGrowthCurve N D) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [lmGrowthCurve_succ]
  exact Nat.le_add_right _ _

theorem lmGrowthCurve_start_le (N D i : ℕ) :
    D ≤ lmGrowthCurve N D i := by
  simpa using lmGrowthCurve_mono N D (Nat.zero_le i)

/-- Two copies of the natural gain fit inside the exact LM expansion. -/
theorem two_lmGrowthGain_le_expansion
    {N d s : ℕ} (hN : 32 ≤ N) (hd : 1 ≤ d)
    (hcutoff : (d : ℝ) / 128 ≤ (s : ℝ)) (hsN : s ≤ N) :
    (((2 * lmGrowthGain N s : ℕ) : ℝ)) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ) := by
  have hCpos := lmGrowthDenominator_pos (hN.trans' (by omega))
  have hdivisor : lmGrowthDivisor N = 2 * lmGrowthDenominator N := rfl
  have hnat : 2 * lmGrowthGain N s ≤ s / lmGrowthDenominator N := by
    apply (Nat.le_div_iff_mul_le hCpos).2
    rw [lmGrowthGain, hdivisor]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      Nat.div_mul_le_self s (2 * lmGrowthDenominator N)
  have hcastDiv : ((s / lmGrowthDenominator N : ℕ) : ℝ) ≤
      (s : ℝ) / (lmGrowthDenominator N : ℝ) := by
    simpa using (Nat.cast_div_le (α := ℝ)
      (m := s) (n := lmGrowthDenominator N))
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hdenpos : (0 : ℝ) < 9216 * Real.log (N : ℝ) ^ 2 := by positivity
  have hquotient :
      (s : ℝ) / (lmGrowthDenominator N : ℝ) ≤
        (s : ℝ) / (9216 * Real.log (N : ℝ) ^ 2) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg s) hdenpos
      (lmGrowthDenominator_lower N)
  have hnatReal : ((2 * lmGrowthGain N s : ℕ) : ℝ) ≤
      ((s / lmGrowthDenominator N : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hnatReal.trans hcastDiv |>.trans hquotient |>.trans
    (lm_expansion_profile_lower hN hd hcutoff hsN)

private theorem le_two_mul_mul_div {q s : ℕ} (hq : 0 < q)
    (hs : 2 * q ≤ s) : s ≤ 2 * q * (s / q) := by
  have hquot : 2 ≤ s / q := (Nat.le_div_iff_mul_le hq).2 hs
  have hmod := Nat.mod_lt s hq
  have hdecomp := Nat.div_add_mod s q
  nlinarith

theorem lmGrowthCurve_add_mul_gain_le (N D i t : ℕ) :
    lmGrowthCurve N D i + t * lmGrowthGain N (lmGrowthCurve N D i) ≤
      lmGrowthCurve N D (i + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hmono : lmGrowthCurve N D i ≤ lmGrowthCurve N D (i + t) :=
        lmGrowthCurve_mono N D (Nat.le_add_right i t)
      have hgain := lmGrowthGain_mono N hmono
      calc
        lmGrowthCurve N D i + (t + 1) * lmGrowthGain N (lmGrowthCurve N D i)
            = (lmGrowthCurve N D i +
                t * lmGrowthGain N (lmGrowthCurve N D i)) +
              lmGrowthGain N (lmGrowthCurve N D i) := by ring
        _ ≤ lmGrowthCurve N D (i + t) +
              lmGrowthGain N (lmGrowthCurve N D (i + t)) :=
            Nat.add_le_add ih hgain
        _ = lmGrowthCurve N D (i + (t + 1)) := by
          rw [show i + (t + 1) = (i + t) + 1 by omega,
            lmGrowthCurve_succ]

theorem lmGrowthCurve_double_after_block {N D i : ℕ} (hN : 2 ≤ N)
    (hlarge : 2 * lmGrowthDivisor N ≤ lmGrowthCurve N D i) :
    2 * lmGrowthCurve N D i ≤
      lmGrowthCurve N D (i + 2 * lmGrowthDivisor N) := by
  have hdiv := le_two_mul_mul_div (lmGrowthDivisor_pos hN) hlarge
  have hiter := lmGrowthCurve_add_mul_gain_le N D i (2 * lmGrowthDivisor N)
  rw [lmGrowthGain] at hiter
  omega

theorem pow_mul_le_lmGrowthCurve_blocks {N D : ℕ} (hN : 2 ≤ N)
    (hD : 2 * lmGrowthDivisor N ≤ D) (j : ℕ) :
    2 ^ j * D ≤
      lmGrowthCurve N D (2 * lmGrowthDivisor N * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstart : D ≤
          lmGrowthCurve N D (2 * lmGrowthDivisor N * j) :=
        lmGrowthCurve_start_le N D _
      have hlarge : 2 * lmGrowthDivisor N ≤
          lmGrowthCurve N D (2 * lmGrowthDivisor N * j) :=
        hD.trans hstart
      have hdouble := lmGrowthCurve_double_after_block hN hlarge
      calc
        2 ^ (j + 1) * D = 2 * (2 ^ j * D) := by rw [pow_succ]; ring
        _ ≤ 2 * lmGrowthCurve N D (2 * lmGrowthDivisor N * j) := by omega
        _ ≤ lmGrowthCurve N D
              (2 * lmGrowthDivisor N * j + 2 * lmGrowthDivisor N) := hdouble
        _ = lmGrowthCurve N D (2 * lmGrowthDivisor N * (j + 1)) := by
          congr 1

theorem lmGrowthCurve_reaches_half {N D : ℕ} (hN : 32 ≤ N)
    (hD : 2 * lmGrowthDivisor N ≤ D) :
    N / 2 + 1 ≤ lmGrowthCurve N D (lmGrowthRounds N) := by
  have hpow := pow_mul_le_lmGrowthCurve_blocks
    (N := N) (D := D) (hN.trans' (by omega)) hD (Nat.log 2 N + 1)
  have hpowN : N < 2 ^ (Nat.log 2 N + 1) :=
    Nat.lt_pow_succ_log_self (by omega : 1 < 2) N
  have hDpos : 0 < D := by
    have := lmGrowthDivisor_pos (hN.trans' (by omega))
    omega
  rw [lmGrowthRounds]
  have : N < lmGrowthCurve N D
      (2 * lmGrowthDivisor N * (Nat.log 2 N + 1)) := by
    exact hpowN.trans_le ((Nat.le_mul_of_pos_right _ hDpos).trans hpow)
  omega

/-- Seven copies of the concrete recurrence fit inside the
`800/epsilon * log(N)^3` radius used in the source.  This is the connector
radius inequality of Lemma 3.15, with an explicit constant. -/
theorem seven_mul_lmGrowthRounds_le_lmRadius {N : ℕ} (hN : 32 ≤ N) :
    7 * lmGrowthRounds N ≤ Parameters.lmRadius (1 / 1024) N := by
  let L := Real.log (N : ℝ)
  let C := lmGrowthDenominator N
  let k := Nat.log 2 N
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNreal : (32 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hLone : (1 : ℝ) ≤ L := by
    apply (Real.le_log_iff_exp_le hNpos).2
    have he := Real.exp_one_lt_d9
    linarith
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hxone : (1 : ℝ) ≤ 9216 * L ^ 2 := by
    have hsq : 1 ≤ L ^ 2 := one_le_pow₀ hLone
    nlinarith
  have hClt : (C : ℝ) < 9216 * L ^ 2 + 1 := by
    dsimp [C, lmGrowthDenominator, L]
    exact Nat.ceil_lt_add_one (by positivity)
  have hC : (C : ℝ) ≤ 9217 * L ^ 2 := by
    have hsq : 1 ≤ L ^ 2 := one_le_pow₀ hLone
    linarith
  have hpowNat : 2 ^ k ≤ N := by
    exact Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  have hpowReal : (((2 ^ k : ℕ) : ℝ)) ≤ (N : ℝ) := by
    exact_mod_cast hpowNat
  have hlogPow : (k : ℝ) * Real.log 2 ≤ L := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ))
      hpowReal
    simpa [L, Real.log_pow] using h
  have hk : (k : ℝ) ≤ 2 * L := by
    have hlogTwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hfactor : (k : ℝ) + 1 ≤ 3 * L := by linarith
  have hroundReal : (lmGrowthRounds N : ℝ) ≤ 110604 * L ^ 3 := by
    calc
      (lmGrowthRounds N : ℝ) = 2 * (2 * (C : ℝ)) * ((k : ℝ) + 1) := by
        simp only [lmGrowthRounds, lmGrowthDivisor, C, k, Nat.cast_mul,
          Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      _ ≤ 2 * (2 * (9217 * L ^ 2)) * ((k : ℝ) + 1) := by
        gcongr
      _ ≤ 2 * (2 * (9217 * L ^ 2)) * (3 * L) := by
        gcongr
      _ = 110604 * L ^ 3 := by ring
  have hradius := Parameters.lmRadius_lower (1 / 1024 : ℝ) N
  have hconstant : 774228 * L ^ 3 ≤
      (1600 / (1 / 1024 : ℝ)) * Real.log (N : ℝ) ^ 3 := by
    dsimp [L]
    norm_num
    nlinarith [pow_nonneg hLpos.le]
  have hreal : ((7 * lmGrowthRounds N : ℕ) : ℝ) ≤
      (Parameters.lmRadius (1 / 1024) N : ℝ) := by
    push_cast
    calc
      (7 : ℝ) * lmGrowthRounds N ≤ 7 * (110604 * L ^ 3) :=
        mul_le_mul_of_nonneg_left hroundReal (by norm_num)
      _ = 774228 * L ^ 3 := by ring
      _ ≤ _ := hconstant.trans hradius
  exact_mod_cast hreal

/-- Five copies are the output radius of source Lemma 3.11. -/
theorem five_mul_lmGrowthRounds_le_lmRadius {N : ℕ} (hN : 32 ≤ N) :
    5 * lmGrowthRounds N ≤ Parameters.lmRadius (1 / 1024) N :=
  (by omega : 5 * lmGrowthRounds N ≤ 7 * lmGrowthRounds N) |>.trans
    (seven_mul_lmGrowthRounds_le_lmRadius hN)

/-- Four-copy form of `seven_mul_lmGrowthRounds_le_lmRadius`. -/
theorem four_mul_lmGrowthRounds_le_lmRadius {N : ℕ} (hN : 32 ≤ N) :
    4 * lmGrowthRounds N ≤ Parameters.lmRadius (1 / 1024) N := by
  have h47 : 4 * lmGrowthRounds N ≤ 7 * lmGrowthRounds N := by omega
  exact h47.trans (seven_mul_lmGrowthRounds_le_lmRadius hN)

/-- Two-copy form of `seven_mul_lmGrowthRounds_le_lmRadius`. -/
theorem two_mul_lmGrowthRounds_le_lmRadius {N : ℕ} (hN : 32 ≤ N) :
    2 * lmGrowthRounds N ≤ Parameters.lmRadius (1 / 1024) N :=
  (by omega : 2 * lmGrowthRounds N ≤ 7 * lmGrowthRounds N) |>.trans
    (seven_mul_lmGrowthRounds_le_lmRadius hN)

/-- One-copy form of `four_mul_lmGrowthRounds_le_lmRadius`. -/
theorem lmGrowthRounds_le_lmRadius {N : ℕ} (hN : 32 ≤ N) :
    lmGrowthRounds N ≤ Parameters.lmRadius (1 / 1024) N :=
  (Nat.le_mul_of_pos_left _ (by omega : 0 < 2)).trans
    (two_mul_lmGrowthRounds_le_lmRadius hN)

/-! ## The adaptive preliminary growth used in Lemma 3.11 -/

/-- Above the LM cutoff, the number of new vertices supplied by the exact
profile is monotone in the size of the growing set.  The point of retaining
the exact profile here is that the preliminary Lemma 3.11 balls may start at
order `d`, even when the ambient order is arbitrarily larger than `d`.

After the substitution `x = 960s/d`, the assertion is the elementary
monotonicity of `x / log(x)^2` on `[exp 2, infinity)`.  Mathlib's monotonicity
of `log(x)/sqrt(x)` gives this without differentiating the LM profile. -/
theorem lm311_expansion_product_mono
    {d a b : ℕ} (hd : 1 ≤ d)
    (ha : (d : ℝ) / 128 ≤ (a : ℝ)) (hab : a ≤ b) :
    expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) a * (a : ℝ) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) b * (b : ℝ) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hd)
  have habReal : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hcutA : ((1 / 64) * (d : ℝ)) / 5 ≤ (a : ℝ) := by
    norm_num at ha ⊢
    linarith
  have hcutB : ((1 / 64) * (d : ℝ)) / 5 ≤ (b : ℝ) :=
    hcutA.trans habReal
  rw [expansionEpsilon_of_le hcutA, expansionEpsilon_of_le hcutB]
  let x : ℝ := 960 * (a : ℝ) / (d : ℝ)
  let y : ℝ := 960 * (b : ℝ) / (d : ℝ)
  have hxy : x ≤ y := by
    dsimp [x, y]
    exact (div_le_div_iff_of_pos_right hdpos).2
      (mul_le_mul_of_nonneg_left habReal (by norm_num))
  have hx75 : (15 : ℝ) / 2 ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ hdpos]
    nlinarith
  have hexpTwo : Real.exp 2 < (15 : ℝ) / 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hxexp : Real.exp 2 ≤ x := hexpTwo.le.trans hx75
  have hyexp : Real.exp 2 ≤ y := hxexp.trans hxy
  have hxpos : 0 < x := (Real.exp_pos 2).trans_le hxexp
  have hypos : 0 < y := hxpos.trans_le hxy
  have hsqrtx : 0 < √x := Real.sqrt_pos.2 hxpos
  have hsqrty : 0 < √y := Real.sqrt_pos.2 hypos
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith [hx75])
  have hlogy : 0 < Real.log y := hlogx.trans_le (Real.log_le_log hxpos hxy)
  have hanti : Real.log y / √y ≤ Real.log x / √x :=
    Real.log_div_sqrt_antitoneOn hxexp hyexp hxy
  have hcrossSqrt : Real.log y * √x ≤ Real.log x * √y := by
    exact (div_le_div_iff₀ hsqrty hsqrtx).mp hanti
  have hcrossSq :
      (Real.log y * √x) ^ 2 ≤ (Real.log x * √y) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hlogy.le hsqrtx.le)
      (mul_nonneg hlogx.le hsqrty.le)).2 hcrossSqrt
  have hcross : x * Real.log y ^ 2 ≤ y * Real.log x ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hxpos.le, Real.sq_sqrt hypos.le] at hcrossSq
    nlinarith
  have hratio : x / Real.log x ^ 2 ≤ y / Real.log y ^ 2 := by
    exact (div_le_div_iff₀ (sq_pos_of_pos hlogx) (sq_pos_of_pos hlogy)).2 hcross
  have hscale : (0 : ℝ) ≤ (d : ℝ) / (960 * 1024) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hratio hscale
  calc
    (1 / 1024) / Real.log (15 * (a : ℝ) / ((1 / 64) * (d : ℝ))) ^ 2 *
          (a : ℝ)
        = (d : ℝ) / (960 * 1024) * (x / Real.log x ^ 2) := by
          dsimp [x]
          field_simp
          <;> ring_nf
    _ ≤ (d : ℝ) / (960 * 1024) * (y / Real.log y ^ 2) := hscaled
    _ = (1 / 1024) /
          Real.log (15 * (b : ℝ) / ((1 / 64) * (d : ℝ))) ^ 2 * (b : ℝ) := by
          dsimp [y]
          field_simp
          <;> ring_nf

/-- One quarter of the exact LM expansion, rounded down.  One quarter is
used for certified growth; the remaining three quarters absorb the finite
barriers and the rounding loss in Lemma 3.11. -/
noncomputable def lm311AdaptiveGain (d s : ℕ) : ℕ :=
  ⌊(expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)) / 4⌋₊

/-- The exact-profile preliminary recurrence. -/
noncomputable def lm311AdaptiveCurve (d start : ℕ) : ℕ → ℕ
  | 0 => start
  | i + 1 => lm311AdaptiveCurve d start i +
      lm311AdaptiveGain d (lm311AdaptiveCurve d start i)

theorem four_lm311AdaptiveGain_le_expansion (d s : ℕ) :
    (((4 * lm311AdaptiveGain d s : ℕ) : ℝ)) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ) := by
  have hnonneg : 0 ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ) :=
    mul_nonneg (expansionEpsilon_nonneg (by norm_num) s) (Nat.cast_nonneg s)
  have hfloor : (lm311AdaptiveGain d s : ℝ) ≤
      (expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)) / 4 := by
    exact Nat.floor_le (div_nonneg hnonneg (by norm_num))
  push_cast
  linarith

theorem lm311AdaptiveGain_mono_above
    {d a b : ℕ} (hd : 1 ≤ d)
    (ha : (d : ℝ) / 128 ≤ (a : ℝ)) (hab : a ≤ b) :
    lm311AdaptiveGain d a ≤ lm311AdaptiveGain d b := by
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_right
    (lm311_expansion_product_mono hd ha hab) (by norm_num)

@[simp] theorem lm311AdaptiveCurve_zero (d start : ℕ) :
    lm311AdaptiveCurve d start 0 = start := rfl

@[simp] theorem lm311AdaptiveCurve_succ (d start i : ℕ) :
    lm311AdaptiveCurve d start (i + 1) =
      lm311AdaptiveCurve d start i +
        lm311AdaptiveGain d (lm311AdaptiveCurve d start i) := rfl

theorem lm311AdaptiveCurve_mono (d start : ℕ) :
    Monotone (lm311AdaptiveCurve d start) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [lm311AdaptiveCurve_succ]
  exact Nat.le_add_right _ _

theorem lm311AdaptiveCurve_start_le (d start i : ℕ) :
    start ≤ lm311AdaptiveCurve d start i := by
  simpa using lm311AdaptiveCurve_mono d start (Nat.zero_le i)

theorem lm311AdaptiveCurve_add_mul_gain_le
    {d start i t : ℕ} (hd : 1 ≤ d)
    (hstart : (d : ℝ) / 128 ≤ (start : ℝ)) :
    lm311AdaptiveCurve d start i +
        t * lm311AdaptiveGain d (lm311AdaptiveCurve d start i) ≤
      lm311AdaptiveCurve d start (i + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hmono : lm311AdaptiveCurve d start i ≤
          lm311AdaptiveCurve d start (i + t) :=
        lm311AdaptiveCurve_mono d start (Nat.le_add_right i t)
      have hcut : (d : ℝ) / 128 ≤
          (lm311AdaptiveCurve d start i : ℝ) := by
        exact hstart.trans (by exact_mod_cast lm311AdaptiveCurve_start_le d start i)
      have hgain := lm311AdaptiveGain_mono_above hd hcut hmono
      calc
        lm311AdaptiveCurve d start i +
              (t + 1) * lm311AdaptiveGain d (lm311AdaptiveCurve d start i)
            = (lm311AdaptiveCurve d start i +
                t * lm311AdaptiveGain d (lm311AdaptiveCurve d start i)) +
              lm311AdaptiveGain d (lm311AdaptiveCurve d start i) := by ring
        _ ≤ lm311AdaptiveCurve d start (i + t) +
              lm311AdaptiveGain d (lm311AdaptiveCurve d start (i + t)) :=
            Nat.add_le_add ih hgain
        _ = lm311AdaptiveCurve d start (i + (t + 1)) := by
          rw [show i + (t + 1) = (i + t) + 1 by omega,
            lm311AdaptiveCurve_succ]

/-- Rate form used directly by the variable schedules in `LM311Numerics`.
It remains only to show that the phase-specific barrier is no larger than
the adaptive gain at the lower curve value. -/
theorem lm311AdaptiveGain_add_cost_le_expansion
    {d lower s cost : ℕ} (hd : 1 ≤ d)
    (hlower : (d : ℝ) / 128 ≤ (lower : ℝ))
    (hls : lower ≤ s) (hcost : cost ≤ lm311AdaptiveGain d lower) :
    ((((lm311AdaptiveGain d lower + cost : ℕ) : ℝ))) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ) := by
  have hgainMono := lm311AdaptiveGain_mono_above hd hlower hls
  have hfour := four_lm311AdaptiveGain_le_expansion d s
  have hnat : lm311AdaptiveGain d lower + cost ≤
      4 * lm311AdaptiveGain d s := by omega
  have hnatReal : (((lm311AdaptiveGain d lower + cost : ℕ) : ℝ)) ≤
      (((4 * lm311AdaptiveGain d s : ℕ) : ℝ)) := by exact_mod_cast hnat
  exact hnatReal.trans hfour

/-- A deliberately generous absolute degree threshold.  It absorbs all
integer roundoff and all polynomial-in-the-stage-index barriers in the
adaptive Lemma 3.11 schedules. -/
def lm311DegreeThreshold : ℕ := 2 ^ 60

/-- The common retained radius-one seed for the prescribed roots. -/
def lm311AdaptiveSeed (d : ℕ) : ℕ := d / 128 + 1

theorem lm311AdaptiveSeed_cutoff (d : ℕ) :
    (d : ℝ) / 128 ≤ (lm311AdaptiveSeed d : ℝ) := by
  have hmod := Nat.mod_lt d (by norm_num : 0 < 128)
  have hdecomp := Nat.div_add_mod d 128
  have hnat : d ≤ 128 * (d / 128 + 1) := by omega
  have hreal : (d : ℝ) ≤ 128 * (d / 128 + 1 : ℕ) := by exact_mod_cast hnat
  norm_num [lm311AdaptiveSeed] at hreal ⊢
  linarith

theorem lm311AdaptiveSeed_large {d : ℕ} (hd : lm311DegreeThreshold ≤ d) :
    2 ^ 53 ≤ lm311AdaptiveSeed d := by
  dsimp [lm311DegreeThreshold, lm311AdaptiveSeed] at hd ⊢
  have hquot : 2 ^ 53 ≤ d / 128 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 128)).2
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hd
  omega

theorem lm311AdaptiveSeed_le_source_seeds {d : ℕ}
    (hd : lm311DegreeThreshold ≤ d) :
    lm311AdaptiveSeed d ≤ lm311HighRootSeed d 2 0 ∧
      lm311AdaptiveSeed d ≤ lm311ReservoirSeed d 2 0 ∧
      lm311AdaptiveSeed d ≤ lm311LowRootSeed d 2 0 := by
  have hseed := lm311AdaptiveSeed_large hd
  have hdlarge : 128 ≤ d := by
    exact hd.trans' (by norm_num [lm311DegreeThreshold])
  have hquot : d / 128 + 24 ≤ d := by
    have hdiv : d / 128 ≤ d := Nat.div_le_self _ _
    omega
  dsimp [lm311AdaptiveSeed, lm311HighRootSeed, lm311HighFixedBudget,
    lm311ReservoirSeed, lm311LowRootSeed]
  norm_num
  omega

private theorem lm311_log_stage_bound (j : ℕ) :
    Real.log (15 * (8 : ℝ) ^ j) ≤ 3 * (j + 2) := by
  have hlog15 : Real.log 15 < 3 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 15)]
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
  have hlog8 : Real.log 8 < 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    have hlogTwo : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
      nlinarith [Real.exp_one_gt_d9]
    have hthree := mul_lt_mul_of_pos_left hlogTwo (by norm_num : (0 : ℝ) < 3)
    norm_num at hthree ⊢
    exact hthree
  rw [Real.log_mul (by norm_num : (15 : ℝ) ≠ 0) (by positivity), Real.log_pow]
  push_cast
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

private theorem lm311_stage_square_le (j : ℕ) :
    (j + 2) ^ 2 ≤ 4 * 8 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [pow_succ]
      have hpoly : (j + 3) ^ 2 ≤ 8 * (j + 2) ^ 2 := by
        calc
          (j + 3) ^ 2 ≤ (j + 3) ^ 2 + (7 * j ^ 2 + 26 * j + 23) :=
            Nat.le_add_right _ _
          _ = 8 * (j + 2) ^ 2 := by ring
      calc
        (j + 3) ^ 2 ≤ 8 * (j + 2) ^ 2 := hpoly
        _ ≤ 8 * (4 * 8 ^ j) := Nat.mul_le_mul_left 8 ih
        _ = 4 * (8 ^ j * 8) := by ring

private theorem lm311_stage_fifth_le (j : ℕ) :
    (j + 2) ^ 5 ≤ 32 * 8 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [pow_succ]
      have hpoly : (j + 3) ^ 5 ≤ 8 * (j + 2) ^ 5 := by
        calc
          (j + 3) ^ 5 ≤ (j + 3) ^ 5 +
              (7 * j ^ 5 + 65 * j ^ 4 + 230 * j ^ 3 +
                370 * j ^ 2 + 235 * j + 13) := Nat.le_add_right _ _
          _ = 8 * (j + 2) ^ 5 := by ring
      calc
        (j + 3) ^ 5 ≤ 8 * (j + 2) ^ 5 := hpoly
        _ ≤ 8 * (32 * 8 ^ j) := Nat.mul_le_mul_left 8 ih
        _ = 32 * (8 ^ j * 8) := by ring

theorem lm311AdaptiveBlock_pos (j : ℕ) :
    0 < Parameters.lm311AdaptiveBlock j := by
  simp [Parameters.lm311AdaptiveBlock]

theorem lm311AdaptiveTime_strictMono :
    StrictMono Parameters.lm311AdaptiveTime := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [Parameters.lm311AdaptiveTime]
  have := lm311AdaptiveBlock_pos j
  omega

theorem lm311AdaptiveTime_index_le (j : ℕ) :
    j ≤ Parameters.lm311AdaptiveTime j := by
  induction j with
  | zero => simp [Parameters.lm311AdaptiveTime]
  | succ j ih =>
      rw [Parameters.lm311AdaptiveTime]
      have := lm311AdaptiveBlock_pos j
      omega

/-- At the beginning of stage `j`, one certified adaptive increment is at
least the stage base divided by its quadratic block length. -/
theorem lm311AdaptiveGain_stage_lower
    {d j : ℕ} (hd : lm311DegreeThreshold ≤ d) :
    (8 ^ j * lm311AdaptiveSeed d) /
        Parameters.lm311AdaptiveBlock j ≤
      lm311AdaptiveGain d (8 ^ j * lm311AdaptiveSeed d) := by
  let base := 8 ^ j * lm311AdaptiveSeed d
  let block := Parameters.lm311AdaptiveBlock j
  have hd1 : 1 ≤ d := le_trans (by norm_num [lm311DegreeThreshold]) hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hd1)
  have hseedCut := lm311AdaptiveSeed_cutoff d
  have hbaseCut : (d : ℝ) / 128 ≤ (base : ℝ) := by
    have hpow : 1 ≤ 8 ^ j := Nat.one_le_pow j 8 (by norm_num)
    have hseed : lm311AdaptiveSeed d ≤ base := by
      dsimp [base]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    exact hseedCut.trans (by exact_mod_cast hseed)
  have hprofileCut : ((1 / 64) * (d : ℝ)) / 5 ≤ (base : ℝ) := by
    norm_num at hbaseCut ⊢
    linarith
  have hseedUpper : lm311AdaptiveSeed d ≤ d / 64 := by
    dsimp [lm311AdaptiveSeed]
    have hd128 : 128 ≤ d := hd.trans' (by norm_num [lm311DegreeThreshold])
    have hsplit : d / 128 + 1 ≤ d / 64 := by omega
    exact hsplit
  have hratioUpper : 960 * (base : ℝ) / (d : ℝ) ≤ 15 * (8 : ℝ) ^ j := by
    have hseedReal : (lm311AdaptiveSeed d : ℝ) ≤ (d : ℝ) / 64 := by
      have hcast : (lm311AdaptiveSeed d : ℝ) ≤ (d / 64 : ℕ) := by
        exact_mod_cast hseedUpper
      exact hcast.trans (by simpa using
        (Nat.cast_div_le (α := ℝ) (m := d) (n := 64)))
    have hmul : (8 : ℝ) ^ j * (lm311AdaptiveSeed d : ℝ) ≤
        (8 : ℝ) ^ j * ((d : ℝ) / 64) :=
      mul_le_mul_of_nonneg_left hseedReal (by positivity)
    calc
      960 * (base : ℝ) / (d : ℝ)
          = 960 * ((8 : ℝ) ^ j * (lm311AdaptiveSeed d : ℝ)) / (d : ℝ) := by
            simp [base]
      _ ≤ 960 * ((8 : ℝ) ^ j * ((d : ℝ) / 64)) / (d : ℝ) := by
        exact (div_le_div_iff_of_pos_right hdpos).2
          (mul_le_mul_of_nonneg_left hmul (by norm_num))
      _ = 15 * (8 : ℝ) ^ j := by field_simp <;> ring
  have hratioLower : (15 : ℝ) / 2 ≤ 960 * (base : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdpos]
    have hseedReal : (d : ℝ) / 128 ≤ (lm311AdaptiveSeed d : ℝ) := hseedCut
    have hpow : (1 : ℝ) ≤ (8 : ℝ) ^ j := by
      exact_mod_cast Nat.one_le_pow j 8 (by norm_num)
    have hmul := mul_le_mul hpow hseedReal (by positivity) (by positivity)
    dsimp [base]
    push_cast
    nlinarith
  have hlogpos : 0 < Real.log (960 * (base : ℝ) / (d : ℝ)) :=
    Real.log_pos (by linarith)
  have hlogUpper : Real.log (960 * (base : ℝ) / (d : ℝ)) ≤
      3 * (j + 2) := by
    exact (Real.log_le_log (by positivity) hratioUpper).trans
      (lm311_log_stage_bound j)
  have hden :
      4096 * Real.log (960 * (base : ℝ) / (d : ℝ)) ^ 2 ≤ (block : ℝ) := by
    dsimp [block, Parameters.lm311AdaptiveBlock]
    push_cast
    nlinarith [sq_nonneg (3 * ((j : ℝ) + 2) -
      Real.log (960 * (base : ℝ) / (d : ℝ)))]
  have hblockpos : (0 : ℝ) < (block : ℝ) := by
    exact_mod_cast lm311AdaptiveBlock_pos j
  have hdenpos : 0 < 4096 * Real.log (960 * (base : ℝ) / (d : ℝ)) ^ 2 := by
    positivity
  have hcastDiv : (((base / block : ℕ) : ℝ)) ≤ (base : ℝ) / (block : ℝ) := by
    simpa using Nat.cast_div_le (α := ℝ) (m := base) (n := block)
  have hreal : (((base / block : ℕ) : ℝ)) ≤
      (expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) base *
        (base : ℝ)) / 4 := by
    rw [expansionEpsilon_of_le hprofileCut]
    have harg : 15 * (base : ℝ) / ((1 / 64) * (d : ℝ)) =
        960 * (base : ℝ) / (d : ℝ) := by field_simp <;> ring
    rw [harg]
    calc
      (((base / block : ℕ) : ℝ)) ≤ (base : ℝ) / (block : ℝ) := hcastDiv
      _ ≤ (base : ℝ) /
          (4096 * Real.log (960 * (base : ℝ) / (d : ℝ)) ^ 2) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg base) hdenpos hden
      _ = ((1 / 1024 : ℝ) /
          Real.log (960 * (base : ℝ) / (d : ℝ)) ^ 2 * (base : ℝ)) / 4 := by
        field_simp <;> ring
  dsimp [lm311AdaptiveGain]
  exact Nat.le_floor hreal

private theorem lm311_stage_base_large
    {d j : ℕ} (hd : lm311DegreeThreshold ≤ d) :
    2 * Parameters.lm311AdaptiveBlock j ≤
      8 ^ j * lm311AdaptiveSeed d := by
  have hseed := lm311AdaptiveSeed_large hd
  have hsq := lm311_stage_square_le j
  dsimp [Parameters.lm311AdaptiveBlock]
  calc
    2 * (65536 * (j + 2) ^ 2)
        ≤ 2 * (65536 * (4 * 8 ^ j)) := by omega
    _ ≤ 8 ^ j * lm311AdaptiveSeed d := by
      have : 2 * 65536 * 4 ≤ 2 ^ 53 := by norm_num
      nlinarith [show 0 < 8 ^ j by positivity]

/-- After the `j`th explicit clock checkpoint the adaptive recurrence has
grown by a factor `8^j`. -/
theorem lm311AdaptiveCurve_checkpoint
    {d j : ℕ} (hd : lm311DegreeThreshold ≤ d) :
    8 ^ j * lm311AdaptiveSeed d ≤
      lm311AdaptiveCurve d (lm311AdaptiveSeed d)
        (Parameters.lm311AdaptiveTime j) := by
  induction j with
  | zero => simp [Parameters.lm311AdaptiveTime]
  | succ j ih =>
      let current := lm311AdaptiveCurve d (lm311AdaptiveSeed d)
        (Parameters.lm311AdaptiveTime j)
      let base := 8 ^ j * lm311AdaptiveSeed d
      let block := Parameters.lm311AdaptiveBlock j
      have hd1 : 1 ≤ d := le_trans (by norm_num [lm311DegreeThreshold]) hd
      have hcut : (d : ℝ) / 128 ≤ (lm311AdaptiveSeed d : ℝ) :=
        lm311AdaptiveSeed_cutoff d
      have hiterate := lm311AdaptiveCurve_add_mul_gain_le
        (d := d) (start := lm311AdaptiveSeed d)
        (i := Parameters.lm311AdaptiveTime j) (t := 14 * block) hd1 hcut
      have hgainMono : lm311AdaptiveGain d base ≤ lm311AdaptiveGain d current := by
        apply lm311AdaptiveGain_mono_above hd1
        · exact hcut.trans (by exact_mod_cast
            (Nat.le_mul_of_pos_left (lm311AdaptiveSeed d) (by positivity : 0 < 8 ^ j)))
        · exact ih
      have hbaseDiv := lm311AdaptiveGain_stage_lower (d := d) (j := j) hd
      have hlarge := lm311_stage_base_large (d := d) (j := j) hd
      have hgrow : 8 * base ≤ current + 14 * block * lm311AdaptiveGain d current := by
        have hdiv := le_two_mul_mul_div (lm311AdaptiveBlock_pos j) hlarge
        have hgain : base / block ≤ lm311AdaptiveGain d current :=
          hbaseDiv.trans hgainMono
        dsimp [base, block, current] at hdiv hgain ⊢
        nlinarith
      rw [Parameters.lm311AdaptiveTime]
      have hstep := hgrow.trans hiterate
      simpa [base, block, current, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hstep

theorem lm311AdaptiveCurve_reaches_warmTarget
    {n d : ℕ} (hd : lm311DegreeThreshold ≤ d)
    (hD : 0 < Parameters.lmExpansionOrder n) :
    Parameters.lmExpansionOrder n ^ 4 ≤
      lm311AdaptiveCurve d (lm311AdaptiveSeed d)
        (Parameters.lm311AdaptiveRounds n) := by
  let target := Parameters.lmExpansionOrder n ^ 4
  let stages := Parameters.lm311AdaptiveStages n
  have htarget : target < 8 ^ stages := by
    dsimp [stages, Parameters.lm311AdaptiveStages]
    exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 8) target
  have hcheckpoint := lm311AdaptiveCurve_checkpoint (d := d) (j := stages) hd
  have hseedPos : 0 < lm311AdaptiveSeed d := by simp [lm311AdaptiveSeed]
  have : target ≤ 8 ^ stages * lm311AdaptiveSeed d := by
    exact htarget.le.trans (Nat.le_mul_of_pos_right _ hseedPos)
  simpa [target, stages, Parameters.lm311AdaptiveRounds] using this.trans hcheckpoint

/-- Stage of the adaptive clock containing round `i`. -/
noncomputable def lm311AdaptiveStageAt (i : ℕ) : ℕ :=
  Nat.findGreatest (fun j ↦ Parameters.lm311AdaptiveTime j ≤ i) i

theorem lm311AdaptiveTime_stageAt_le (i : ℕ) :
    Parameters.lm311AdaptiveTime (lm311AdaptiveStageAt i) ≤ i := by
  apply Nat.findGreatest_spec (P := fun j ↦ Parameters.lm311AdaptiveTime j ≤ i)
    (Nat.zero_le i)
  simp [Parameters.lm311AdaptiveTime]

theorem lt_lm311AdaptiveTime_stageAt_succ (i : ℕ) :
    i < Parameters.lm311AdaptiveTime (lm311AdaptiveStageAt i + 1) := by
  by_cases hnext : lm311AdaptiveStageAt i + 1 ≤ i
  · have hnot := Nat.findGreatest_is_greatest
      (P := fun j ↦ Parameters.lm311AdaptiveTime j ≤ i)
      (Nat.lt_succ_self (lm311AdaptiveStageAt i)) hnext
    exact lt_of_not_ge hnot
  · have hi : i < lm311AdaptiveStageAt i + 1 := by omega
    exact hi.trans_le (lm311AdaptiveTime_index_le _)

/-- Every phase-specific local barrier in the `k=2`, empty-reserved-set
instance is bounded by `6i+40`; the adaptive gain dominates this quantity
uniformly at the very large absolute degree threshold. -/
theorem lm311AdaptiveCost_le_gain
    {d i : ℕ} (hd : lm311DegreeThreshold ≤ d) :
    6 * i + 40 ≤
      lm311AdaptiveGain d
        (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i) := by
  let j := lm311AdaptiveStageAt i
  let base := 8 ^ j * lm311AdaptiveSeed d
  let block := Parameters.lm311AdaptiveBlock j
  have htime := lm311AdaptiveTime_stageAt_le i
  have hnext := lt_lm311AdaptiveTime_stageAt_succ i
  have hcheckpoint := lm311AdaptiveCurve_checkpoint (d := d) (j := j) hd
  have hcurveTime :
      lm311AdaptiveCurve d (lm311AdaptiveSeed d)
          (Parameters.lm311AdaptiveTime j) ≤
        lm311AdaptiveCurve d (lm311AdaptiveSeed d) i :=
    lm311AdaptiveCurve_mono d (lm311AdaptiveSeed d) htime
  have hbaseCurve : base ≤
      lm311AdaptiveCurve d (lm311AdaptiveSeed d) i :=
    hcheckpoint.trans hcurveTime
  have hd1 : 1 ≤ d := le_trans (by norm_num [lm311DegreeThreshold]) hd
  have hcutBase : (d : ℝ) / 128 ≤ (base : ℝ) := by
    have hseedCut := lm311AdaptiveSeed_cutoff d
    have hseedBase : lm311AdaptiveSeed d ≤ base := by
      dsimp [base]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    exact hseedCut.trans (by exact_mod_cast hseedBase)
  have hgainMono : lm311AdaptiveGain d base ≤
      lm311AdaptiveGain d
        (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i) :=
    lm311AdaptiveGain_mono_above hd1 hcutBase hbaseCurve
  have hbaseGain := lm311AdaptiveGain_stage_lower (d := d) (j := j) hd
  have htimeUpper := Parameters.lm311AdaptiveTime_le (j + 1)
  have hiUpper : i ≤ 917504 * (j + 1) * (j + 3) ^ 2 := by
    change i < Parameters.lm311AdaptiveTime (j + 1) at hnext
    exact hnext.le.trans htimeUpper
  have hcostUpper : 6 * i + 40 ≤ 5505064 * (j + 3) ^ 3 := by
    have hprod : (j + 1) * (j + 3) ^ 2 ≤ (j + 3) ^ 3 := by
      calc
        (j + 1) * (j + 3) ^ 2 ≤ (j + 3) * (j + 3) ^ 2 := by
          exact Nat.mul_le_mul_right _ (by omega)
        _ = (j + 3) ^ 3 := by ring
    have hcubic : 1 ≤ (j + 3) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have hprodScaled :
        917504 * ((j + 1) * (j + 3) ^ 2) ≤
          917504 * (j + 3) ^ 3 :=
      Nat.mul_le_mul_left 917504 hprod
    have hsixScaled :
        6 * (917504 * ((j + 1) * (j + 3) ^ 2)) ≤
          6 * (917504 * (j + 3) ^ 3) :=
      Nat.mul_le_mul_left 6 hprodScaled
    have hfortyScaled : 40 ≤ 40 * (j + 3) ^ 3 := by
      simpa only [mul_one] using Nat.mul_le_mul_left 40 hcubic
    calc
      6 * i + 40 ≤ 6 * (917504 * (j + 1) * (j + 3) ^ 2) + 40 := by omega
      _ ≤ 6 * (917504 * (j + 3) ^ 3) + 40 := by
        exact Nat.add_le_add_right (by simpa [mul_assoc] using hsixScaled) 40
      _ = 5505024 * (j + 3) ^ 3 + 40 := by ring
      _ ≤ 5505024 * (j + 3) ^ 3 + 40 * (j + 3) ^ 3 := by
        exact Nat.add_le_add_left hfortyScaled _
      _ = 5505064 * (j + 3) ^ 3 := by ring
  have hfifth := lm311_stage_fifth_le (j + 1)
  have hblockCost : block * (6 * i + 40) ≤ base := by
    have hseed := lm311AdaptiveSeed_large hd
    calc
      block * (6 * i + 40)
          ≤ (65536 * (j + 3) ^ 2) * (5505064 * (j + 3) ^ 3) := by
            dsimp [block, Parameters.lm311AdaptiveBlock]
            gcongr <;> omega
      _ = (65536 * 5505064) * (j + 3) ^ 5 := by ring
      _ ≤ (65536 * 5505064) * (32 * 8 ^ (j + 1)) := by gcongr
      _ ≤ 8 ^ j * 2 ^ 53 := by
        rw [pow_succ]
        have hcoeff : (65536 * 5505064) * (32 * 8) ≤ 2 ^ 53 := by norm_num
        calc
          (65536 * 5505064) * (32 * (8 ^ j * 8))
              = 8 ^ j * ((65536 * 5505064) * (32 * 8)) := by ring
          _ ≤ 8 ^ j * 2 ^ 53 := Nat.mul_le_mul_left _ hcoeff
      _ ≤ 8 ^ j * lm311AdaptiveSeed d := Nat.mul_le_mul_left _ hseed
      _ = base := by rfl
  have hcostDiv : 6 * i + 40 ≤ base / block :=
    (Nat.le_div_iff_mul_le (lm311AdaptiveBlock_pos j)).2 <| by
      simpa [mul_comm] using hblockCost
  exact hcostDiv.trans hbaseGain |>.trans hgainMono

theorem lm311AdaptiveCurve_mono_start
    {d a b : ℕ} (hd : 1 ≤ d)
    (ha : (d : ℝ) / 128 ≤ (a : ℝ)) (hab : a ≤ b) :
    ∀ i, lm311AdaptiveCurve d a i ≤ lm311AdaptiveCurve d b i := by
  intro i
  induction i with
  | zero => simpa using hab
  | succ i ih =>
      rw [lm311AdaptiveCurve_succ, lm311AdaptiveCurve_succ]
      have hcut : (d : ℝ) / 128 ≤ (lm311AdaptiveCurve d a i : ℝ) :=
        ha.trans (by exact_mod_cast lm311AdaptiveCurve_start_le d a i)
      exact Nat.add_le_add ih (lm311AdaptiveGain_mono_above hd hcut ih)

/-- A carrier pays the fixed cycle, root, and route barriers before its
adaptive growth begins. -/
noncomputable def lm311CarrierCost (n : ℕ) : ℕ :=
  12 + lm311GirthBudget n + 4 * (3 * lmGrowthRounds n + 1)

/-- The carrier starts large enough that half of the globally normalized
gain pays its fixed barrier, but never needs to charge a retained expansion. -/
noncomputable def lm311CarrierStart (n d : ℕ) : ℕ :=
  max (2 * lmGrowthDivisor n * (lm311CarrierCost n + 1))
    (lm311AdaptiveSeed d)

/-- The local phase is followed by the ordinary ambient-size recurrence.
The maximum makes the splice monotone also in the high-degree regime, where
`d/128` can be much larger than every polylogarithmic target. -/
noncomputable def lm311CombinedStart (n start : ℕ) : ℕ :=
  max (Parameters.lmExpansionOrder n ^ 4) start

noncomputable def lm311CombinedGrowth (n d start i : ℕ) : ℕ :=
  if i < Parameters.lm311AdaptiveRounds n then
    lm311AdaptiveCurve d start i
  else
    lmGrowthCurve n (lm311CombinedStart n start)
      (i - Parameters.lm311AdaptiveRounds n)

noncomputable def lm311CombinedGain (n d start i : ℕ) : ℕ :=
  if i < Parameters.lm311AdaptiveRounds n then
    lm311AdaptiveGain d (lm311AdaptiveCurve d start i)
  else
    lmGrowthGain n
      (lmGrowthCurve n (lm311CombinedStart n start)
        (i - Parameters.lm311AdaptiveRounds n))

theorem lm311AdaptiveCurve_reaches_combinedStart
    {n d start : ℕ} (hd : lm311DegreeThreshold ≤ d)
    (hD : 0 < Parameters.lmExpansionOrder n)
    (hstart : lm311AdaptiveSeed d ≤ start) :
    lm311CombinedStart n start ≤
      lm311AdaptiveCurve d start (Parameters.lm311AdaptiveRounds n) := by
  have hd1 : 1 ≤ d := le_trans (by norm_num [lm311DegreeThreshold]) hd
  have hseedCut := lm311AdaptiveSeed_cutoff d
  have hmono := lm311AdaptiveCurve_mono_start hd1 hseedCut hstart
    (Parameters.lm311AdaptiveRounds n)
  have hwarm := lm311AdaptiveCurve_reaches_warmTarget (n := n) (d := d) hd hD
  dsimp [lm311CombinedStart]
  exact max_le (hwarm.trans hmono)
    (lm311AdaptiveCurve_start_le d start _)

theorem lm311CombinedGrowth_zero
    {n d start : ℕ} (hrounds : 0 < Parameters.lm311AdaptiveRounds n) :
    lm311CombinedGrowth n d start 0 = start := by
  simp [lm311CombinedGrowth, hrounds]

theorem lm311Combined_next
    {n d start i : ℕ} (hd : lm311DegreeThreshold ≤ d)
    (hD : 0 < Parameters.lmExpansionOrder n)
    (hstart : lm311AdaptiveSeed d ≤ start) :
    lm311CombinedGrowth n d start (i + 1) ≤
      lm311CombinedGrowth n d start i + lm311CombinedGain n d start i := by
  let r := Parameters.lm311AdaptiveRounds n
  by_cases hi : i < r
  · by_cases hisucc : i + 1 < r
    · have hi' : i < Parameters.lm311AdaptiveRounds n := by simpa [r] using hi
      have hisucc' : i + 1 < Parameters.lm311AdaptiveRounds n := by
        simpa [r] using hisucc
      rw [lm311CombinedGrowth, if_pos hisucc', lm311CombinedGrowth,
        if_pos hi', lm311CombinedGain, if_pos hi', lm311AdaptiveCurve_succ]
    · have hir : i + 1 = r := by omega
      have hsplice := lm311AdaptiveCurve_reaches_combinedStart
        (n := n) (d := d) (start := start) hd hD hstart
      have hboundary : lm311CombinedStart n start ≤
          lm311AdaptiveCurve d start i +
            lm311AdaptiveGain d (lm311AdaptiveCurve d start i) := by
        calc
          lm311CombinedStart n start
              ≤ lm311AdaptiveCurve d start r := hsplice
          _ = lm311AdaptiveCurve d start i +
                lm311AdaptiveGain d (lm311AdaptiveCurve d start i) := by
              rw [← hir, lm311AdaptiveCurve_succ]
      have hi' : i < Parameters.lm311AdaptiveRounds n := by simpa [r] using hi
      have hir' : i + 1 = Parameters.lm311AdaptiveRounds n := by
        simpa [r] using hir
      have hnotSucc : ¬i + 1 < Parameters.lm311AdaptiveRounds n := by omega
      rw [lm311CombinedGrowth, if_neg hnotSucc, lm311CombinedGrowth,
        if_pos hi', lm311CombinedGain, if_pos hi', hir', Nat.sub_self,
        lmGrowthCurve_zero]
      exact hboundary
  · have hisucc : ¬i + 1 < r := by omega
    have hsub : i + 1 - r = (i - r) + 1 := by omega
    have hi' : ¬i < Parameters.lm311AdaptiveRounds n := by simpa [r] using hi
    have hisucc' : ¬i + 1 < Parameters.lm311AdaptiveRounds n := by
      simpa [r] using hisucc
    have hsub' : i + 1 - Parameters.lm311AdaptiveRounds n =
        (i - Parameters.lm311AdaptiveRounds n) + 1 := by simpa [r] using hsub
    rw [lm311CombinedGrowth, if_neg hisucc', lm311CombinedGrowth,
      if_neg hi', lm311CombinedGain, if_neg hi', hsub', lmGrowthCurve_succ]

theorem lm311Combined_lower
    {n d start i : ℕ}
    (hstart : (d : ℝ) / 128 ≤ (start : ℝ)) :
    (d : ℝ) / 128 ≤ (lm311CombinedGrowth n d start i : ℝ) := by
  by_cases hi : i < Parameters.lm311AdaptiveRounds n
  · rw [lm311CombinedGrowth, if_pos hi]
    exact hstart.trans (by exact_mod_cast lm311AdaptiveCurve_start_le d start i)
  · rw [lm311CombinedGrowth, if_neg hi]
    have hs : start ≤ lm311CombinedStart n start := le_max_right _ _
    have hnat := hs.trans (lmGrowthCurve_start_le n (lm311CombinedStart n start)
      (i - Parameters.lm311AdaptiveRounds n))
    have hreal : (start : ℝ) ≤
        (lmGrowthCurve n (lm311CombinedStart n start)
          (i - Parameters.lm311AdaptiveRounds n) : ℝ) := by exact_mod_cast hnat
    exact hstart.trans hreal

theorem lm311Combined_half
    {n d start : ℕ} (hn : 32 ≤ n)
    (hlarge : 2 * lmGrowthDivisor n ≤ lm311CombinedStart n start) :
    n / 2 + 1 ≤ lm311CombinedGrowth n d start
      (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n) := by
  rw [lm311CombinedGrowth, if_neg (by omega :
    ¬Parameters.lm311AdaptiveRounds n + lmGrowthRounds n <
      Parameters.lm311AdaptiveRounds n)]
  simpa using lmGrowthCurve_reaches_half hn hlarge

theorem lm311CarrierCost_le_adaptiveGain
    {n d : ℕ} (hn : 32 ≤ n) (hd : 1 ≤ d)
    (hstartN : lm311CarrierStart n d ≤ n) :
    lm311CarrierCost n ≤ lm311AdaptiveGain d (lm311CarrierStart n d) := by
  let start := lm311CarrierStart n d
  let div := lmGrowthDivisor n
  let cost := lm311CarrierCost n
  have hdiv : 0 < div := lmGrowthDivisor_pos (hn.trans' (by omega))
  have hseed : lm311AdaptiveSeed d ≤ start := le_max_right _ _
  have hcut : (d : ℝ) / 128 ≤ (start : ℝ) :=
    (lm311AdaptiveSeed_cutoff d).trans (by exact_mod_cast hseed)
  have hgrowth : 2 * (cost + 1) ≤ lmGrowthGain n start := by
    apply (Nat.le_div_iff_mul_le hdiv).2
    dsimp [start, lm311CarrierStart, div, lmGrowthGain]
    have := le_max_left
      (2 * lmGrowthDivisor n * (lm311CarrierCost n + 1))
      (lm311AdaptiveSeed d)
    dsimp [cost]
    nlinarith
  have hexp := two_lmGrowthGain_le_expansion hn hd hcut hstartN
  have hreal : (cost : ℝ) ≤
      (expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) start *
        (start : ℝ)) / 4 := by
    have hgrowthReal : ((2 * (cost + 1) : ℕ) : ℝ) ≤
        (lmGrowthGain n start : ℝ) := by exact_mod_cast hgrowth
    push_cast at hexp hgrowthReal
    nlinarith
  dsimp [lm311AdaptiveGain]
  exact Nat.le_floor hreal

theorem lm311CarrierCost_le_adaptiveGain_curve
    {n d i : ℕ} (hn : 32 ≤ n) (hd : 1 ≤ d)
    (hstartN : lm311CarrierStart n d ≤ n) :
    lm311CarrierCost n ≤ lm311AdaptiveGain d
      (lm311AdaptiveCurve d (lm311CarrierStart n d) i) := by
  have hcost := lm311CarrierCost_le_adaptiveGain hn hd hstartN
  have hseed : lm311AdaptiveSeed d ≤ lm311CarrierStart n d := le_max_right _ _
  have hcut : (d : ℝ) / 128 ≤ (lm311CarrierStart n d : ℝ) :=
    (lm311AdaptiveSeed_cutoff d).trans (by exact_mod_cast hseed)
  exact hcost.trans (lm311AdaptiveGain_mono_above hd hcut
    (lm311AdaptiveCurve_start_le d (lm311CarrierStart n d) i))

/-- Global part of a combined schedule.  The caller only has to show that
its complete barrier is no larger than the gain at the polylogarithmic warm
target `D^4`. -/
theorem lm311CombinedGlobal_rate
    {n d start i s cost : ℕ} (hn : 32 ≤ n) (hd : 1 ≤ d)
    (hi : Parameters.lm311AdaptiveRounds n ≤ i)
    (hcut : (d : ℝ) / 128 ≤ (lm311CombinedStart n start : ℝ))
    (hcost : cost ≤ lmGrowthGain n (Parameters.lmExpansionOrder n ^ 4))
    (his : lm311CombinedGrowth n d start i ≤ s) (hsn : s ≤ n / 2) :
    ((((lm311CombinedGain n d start i + cost : ℕ) : ℝ))) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ) := by
  have hi' : ¬i < Parameters.lm311AdaptiveRounds n := by omega
  rw [lm311CombinedGrowth, if_neg hi'] at his
  rw [lm311CombinedGain, if_neg hi']
  have hD4 : Parameters.lmExpansionOrder n ^ 4 ≤ lm311CombinedStart n start :=
    le_max_left _ _
  have hcurveStart := lmGrowthCurve_start_le n (lm311CombinedStart n start)
    (i - Parameters.lm311AdaptiveRounds n)
  have hgainCost : cost ≤ lmGrowthGain n
      (lmGrowthCurve n (lm311CombinedStart n start)
        (i - Parameters.lm311AdaptiveRounds n)) :=
    hcost.trans (lmGrowthGain_mono n (hD4.trans hcurveStart))
  have hgainS := lmGrowthGain_mono n his
  have hcutS : (d : ℝ) / 128 ≤ (s : ℝ) :=
    hcut.trans (by exact_mod_cast hcurveStart.trans his)
  have hsN : s ≤ n := hsn.trans (Nat.div_le_self n 2)
  have hexp := two_lmGrowthGain_le_expansion hn hd hcutS hsN
  have hnat : lmGrowthGain n
        (lmGrowthCurve n (lm311CombinedStart n start)
          (i - Parameters.lm311AdaptiveRounds n)) + cost ≤
      2 * lmGrowthGain n s := by omega
  have hnatReal : ((lmGrowthGain n
        (lmGrowthCurve n (lm311CombinedStart n start)
          (i - Parameters.lm311AdaptiveRounds n)) + cost : ℕ) : ℝ) ≤
      ((2 * lmGrowthGain n s : ℕ) : ℝ) := by exact_mod_cast hnat
  exact hnatReal.trans hexp

noncomputable def lm311GlobalCost (n : ℕ) : ℕ :=
  6 * (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n) +
    lm311CarrierCost n + 4 * Parameters.lmExpansionOrder n ^ 2 + 40

/-- All ambient-order estimates needed by the final `k=2` Lemma 3.11
certificate.  Degree-dependent facts are deliberately absent: the only
degree threshold is the absolute `lm311DegreeThreshold`. -/
structure LM311ScaleBounds (n : ℕ) : Prop where
  card_large : 32 ≤ n
  expansion_pos : 0 < Parameters.lmExpansionOrder n
  local_radius : Parameters.lm311AdaptiveRounds n + 1 ≤
    Parameters.lm311LocalRadius n
  local_fit : 3 * Parameters.lm311LocalRadius n + 2 ≤ lmGrowthRounds n
  carrier_base :
    2 * lmGrowthDivisor n * (lm311CarrierCost n + 1) ≤
      Parameters.lmExpansionOrder n
  warm_large : 2 * lmGrowthDivisor n ≤ Parameters.lmExpansionOrder n ^ 4
  global_cost : lm311GlobalCost n ≤
    lmGrowthGain n (Parameters.lmExpansionOrder n ^ 4)
  packing :
    (4 + (2 + lm311GirthBudget n)) *
        (Parameters.lmExpansionOrder n ^ 2 + 1) ^
          (10 * Parameters.lm311LocalRadius n) <
      n - (8 + lm311GirthBudget n + 2)
  reservoir_half : Parameters.lmExpansionOrder n ^ 2 ≤ n / 2 + 1
  high_star :
    Parameters.lmExpansionOrder n + lm311GirthBudget n + 2 +
        4 * (3 * lmGrowthRounds n + 1) +
        4 * Parameters.lmExpansionOrder n ≤
      Parameters.lmExpansionOrder n ^ 2
  low_star :
    Parameters.lmExpansionOrder n + lm311GirthBudget n + 2 +
        4 * Parameters.lmExpansionOrder n ≤
      Parameters.lmExpansionOrder n ^ 2

theorem eventually_lm311ScaleBounds :
    ∀ᶠ n : ℕ in Filter.atTop, LM311ScaleBounds n := by
  let B : ℝ := 18434
  let M : ℝ := 110604
  let Q : ℝ := 10000000000000000000000000000000000000000
  have hlogtop : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [Filter.eventually_ge_atTop 32,
        hlogtop.eventually (Filter.eventually_ge_atTop Q),
        Parameters.eventually_lm311AdaptiveRounds_succ_le_localRadius,
        Parameters.eventually_lm311LocalRadius_le_lmLogCubeCeil,
        Parameters.eventually_lm311_packing,
        Parameters.eventually_lmExpansionOrder_sq_le_half,
        Parameters.eventually_lm311_star_budgets]
      with n hn hnQ hlocalRadius hlocalCube hpacking hhalf hstars
  let x := Real.log (n : ℝ)
  let D := Parameters.lmExpansionOrder n
  let ell := Parameters.lm311LocalRadius n
  let r := Parameters.lm311AdaptiveRounds n
  let m := lmGrowthRounds n
  let div := lmGrowthDivisor n
  let carrier := lm311CarrierCost n
  have hxQ : Q ≤ x := by simpa [x] using hnQ
  have hxone : (1 : ℝ) ≤ x :=
    (show (1 : ℝ) ≤ Q by norm_num [Q]).trans hxQ
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hq : (lmGrowthDenominator n : ℝ) ≤ 9217 * x ^ 2 := by
    have hlt : (lmGrowthDenominator n : ℝ) < 9216 * x ^ 2 + 1 := by
      simpa [lmGrowthDenominator, x] using
        (Nat.ceil_lt_add_one (by positivity : 0 ≤ 9216 * x ^ 2))
    have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hxone
    linarith
  have hdiv : (div : ℝ) ≤ B * x ^ 2 := by
    dsimp [div, lmGrowthDivisor, B]
    push_cast
    nlinarith
  have hdivpos : 0 < div := lmGrowthDivisor_pos (hn.trans' (by omega))
  have hmUpper : (m : ℝ) ≤ M * x ^ 3 := by
    let k := Nat.log 2 n
    have hpowNat : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have hpowReal : (((2 ^ k : ℕ) : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hpowNat
    have hlogPow : (k : ℝ) * Real.log 2 ≤ x := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ))
        hpowReal
      simpa [x, Real.log_pow] using h
    have hk : (k : ℝ) ≤ 2 * x := by
      have hlogTwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
        nlinarith [Real.log_two_gt_d9]
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    have hk1 : (k : ℝ) + 1 ≤ 3 * x := by linarith
    have hmul : (lmGrowthDenominator n : ℝ) * ((k : ℝ) + 1) ≤
        (9217 * x ^ 2) * (3 * x) := by
      calc
        (lmGrowthDenominator n : ℝ) * ((k : ℝ) + 1)
            ≤ (9217 * x ^ 2) * ((k : ℝ) + 1) :=
              mul_le_mul_of_nonneg_right hq (by positivity)
        _ ≤ (9217 * x ^ 2) * (3 * x) :=
          mul_le_mul_of_nonneg_left hk1 (by positivity)
    dsimp [m, lmGrowthRounds, div, lmGrowthDivisor, M]
    push_cast
    nlinarith
  have hmLower : 36864 * x ^ 3 ≤ (m : ℝ) := by
    let k := Nat.log 2 n
    have hpowN : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by omega : 1 < 2) n
    have hpowReal : (n : ℝ) < (((2 ^ (k + 1) : ℕ) : ℝ)) := by exact_mod_cast hpowN
    have hlog : x ≤ ((k : ℝ) + 1) * Real.log 2 := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ)) hpowReal.le
      simpa [x, Real.log_pow] using h
    have hk : x ≤ (k : ℝ) + 1 := by
      have hlogTwo : Real.log 2 < 1 := by
        rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
        nlinarith [Real.exp_one_gt_d9]
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    have hden := lmGrowthDenominator_lower n
    have hxnonneg : (0 : ℝ) ≤ x := hxpos.le
    have hdennonneg : (0 : ℝ) ≤ (lmGrowthDenominator n : ℝ) :=
      Nat.cast_nonneg _
    have hmul : (9216 * x ^ 2) * x ≤
        (lmGrowthDenominator n : ℝ) * ((k : ℝ) + 1) := by
      calc
        (9216 * x ^ 2) * x
            ≤ (lmGrowthDenominator n : ℝ) * x :=
              mul_le_mul_of_nonneg_right hden hxnonneg
        _ ≤ (lmGrowthDenominator n : ℝ) * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hk hdennonneg
    dsimp [m, lmGrowthRounds, div, lmGrowthDivisor]
    push_cast
    calc
      36864 * x ^ 3 = 4 * ((9216 * x ^ 2) * x) := by ring
      _ ≤ 4 * ((lmGrowthDenominator n : ℝ) * ((k : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 2 * (2 * (lmGrowthDenominator n : ℝ)) * ((k : ℝ) + 1) := by ring
  have hlogCube : (Parameters.lmLogCubeCeil n : ℝ) ≤ 2 * x ^ 3 := by
    have hlt : (Parameters.lmLogCubeCeil n : ℝ) < x ^ 3 + 1 := by
      simpa [Parameters.lmLogCubeCeil, x] using
        (Nat.ceil_lt_add_one (by positivity : 0 ≤ x ^ 3))
    have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hxone
    linarith
  have hell : (ell : ℝ) ≤ 2 * x ^ 3 := by
    have hcast : (ell : ℝ) ≤ (Parameters.lmLogCubeCeil n : ℝ) := by
      exact_mod_cast hlocalCube
    exact hcast.trans hlogCube
  have hr : (r : ℝ) ≤ 2 * x ^ 3 := by
    have : r ≤ ell := by omega
    have hcast : (r : ℝ) ≤ (ell : ℝ) := by exact_mod_cast this
    exact hcast.trans hell
  have hlocalFit : 3 * ell + 2 ≤ m := by
    have hreal : ((3 * ell + 2 : ℕ) : ℝ) ≤ (m : ℝ) := by
      push_cast
      have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hxone
      nlinarith
    exact_mod_cast hreal
  have hDlow : x ^ 10 ≤ (D : ℝ) := by
    simpa [x, D] using Parameters.lmExpansionOrder_lower n
  have hDup : (D : ℝ) ≤ 2 * x ^ 10 := by
    simpa [x, D] using
      Parameters.lmExpansionOrder_le_two_mul (one_le_pow₀ hxone)
  have hDpos : 0 < D := Parameters.lmExpansionOrder_pos (by omega : 1 < n)
  have hgirth : (lm311GirthBudget n : ℝ) ≤ 4 * x + 4 := by
    dsimp [lm311GirthBudget]
    push_cast
    have hlog := Parameters.natLog_two_le_two_log (by omega : 1 ≤ n)
    change (Nat.log 2 n : ℝ) ≤ 2 * x at hlog
    nlinarith only [hlog]
  have hcarrier : (carrier : ℝ) ≤ 14 * M * x ^ 3 := by
    dsimp [carrier, lm311CarrierCost]
    push_cast
    have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hxone
    have hxle : x ≤ x ^ 3 := by nlinarith [sq_nonneg x]
    nlinarith
  have hcarrierBaseReal :
      ((2 * div * (carrier + 1) : ℕ) : ℝ) ≤ (D : ℝ) := by
    push_cast
    have hcoeff : 2 * B * (14 * M + 1) ≤ x ^ 5 := by
      calc
        2 * B * (14 * M + 1) ≤ Q := by norm_num [B, M, Q]
        _ ≤ x ^ 5 := hxQ.trans (by
          simpa only [pow_one] using pow_le_pow_right₀ hxone (by omega : 1 ≤ 5))
    have hcarrierOne : (carrier : ℝ) + 1 ≤ (14 * M + 1) * x ^ 3 := by
      have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hxone
      nlinarith
    calc
      2 * (div : ℝ) * ((carrier : ℝ) + 1)
          ≤ 2 * (B * x ^ 2) * ((14 * M + 1) * x ^ 3) := by gcongr
      _ = (2 * B * (14 * M + 1)) * x ^ 5 := by ring
      _ ≤ x ^ 5 * x ^ 5 := by gcongr
      _ = x ^ 10 := by ring
      _ ≤ (D : ℝ) := hDlow
  have hcarrierBase : 2 * div * (carrier + 1) ≤ D := by
    exact_mod_cast hcarrierBaseReal
  have hwarmLarge : 2 * div ≤ D ^ 4 := by
    have hDle : D ≤ D ^ 4 := by
      have : 1 ≤ D := hDpos
      simpa only [pow_one] using pow_le_pow_right₀ this (by omega : 1 ≤ 4)
    have hcarrierOnePos : 0 < carrier + 1 := by omega
    have hfactor : 2 * div ≤ 2 * div * (carrier + 1) :=
      Nat.le_mul_of_pos_right _ hcarrierOnePos
    exact hfactor.trans hcarrierBase |>.trans hDle
  have hglobalUpper : (lm311GlobalCost n : ℝ) ≤ 3000000 * x ^ 20 := by
    dsimp [lm311GlobalCost]
    push_cast
    have hDsq : (D : ℝ) ^ 2 ≤ 4 * x ^ 20 := by
      have := pow_le_pow_left₀ (Nat.cast_nonneg D) hDup 2
      nlinarith [pow_nonneg hxpos.le 10]
    have hx3x20 : x ^ 3 ≤ x ^ 20 := pow_le_pow_right₀ hxone (by omega)
    have hx1x20 : x ≤ x ^ 20 :=
      (by simpa only [pow_one] using pow_le_pow_right₀ hxone (by omega : 1 ≤ 20))
    have hr20 : (r : ℝ) ≤ 2 * x ^ 20 :=
      hr.trans (mul_le_mul_of_nonneg_left hx3x20 (by norm_num))
    have hm20 : (m : ℝ) ≤ M * x ^ 20 :=
      hmUpper.trans (mul_le_mul_of_nonneg_left hx3x20 (by positivity))
    have hcarrier20 : (carrier : ℝ) ≤ 14 * M * x ^ 20 :=
      hcarrier.trans (mul_le_mul_of_nonneg_left hx3x20 (by positivity))
    have hDterm : 4 * (D : ℝ) ^ 2 ≤ 16 * x ^ 20 := by
      nlinarith only [hDsq]
    have hforty : (40 : ℝ) ≤ 40 * x ^ 20 := by
      have hx20 : (1 : ℝ) ≤ x ^ 20 := one_le_pow₀ hxone
      nlinarith only [hx20]
    have hrm : (r : ℝ) + (m : ℝ) ≤ (2 + M) * x ^ 20 := by
      nlinarith only [hr20, hm20]
    nlinarith only [hrm, hcarrier20, hDterm, hforty]
  have hglobalProduct : lm311GlobalCost n * div ≤ D ^ 4 := by
    have hcoeff : 3000000 * B ≤ x ^ 18 := by
      calc
        3000000 * B ≤ Q := by norm_num [B, Q]
        _ ≤ x ^ 18 := hxQ.trans (by
          simpa only [pow_one] using pow_le_pow_right₀ hxone (by omega : 1 ≤ 18))
    have hreal : ((lm311GlobalCost n * div : ℕ) : ℝ) ≤ ((D ^ 4 : ℕ) : ℝ) := by
      push_cast
      calc
        (lm311GlobalCost n : ℝ) * (div : ℝ)
            ≤ (3000000 * x ^ 20) * (B * x ^ 2) :=
              mul_le_mul hglobalUpper hdiv (by positivity) (by positivity)
        _ = (3000000 * B) * x ^ 22 := by ring
        _ ≤ x ^ 18 * x ^ 22 := by gcongr
        _ = x ^ 40 := by ring
        _ = (x ^ 10) ^ 4 := by ring
        _ ≤ (D : ℝ) ^ 4 := pow_le_pow_left₀ (pow_nonneg hxpos.le 10) hDlow 4
    exact_mod_cast hreal
  have hglobal : lm311GlobalCost n ≤ lmGrowthGain n (D ^ 4) := by
    exact (Nat.le_div_iff_mul_le hdivpos).2 hglobalProduct
  have hmRadius := lmGrowthRounds_le_lmRadius hn
  have hhighStar : D + lm311GirthBudget n + 2 + 4 * (3 * m + 1) + 4 * D ≤ D ^ 2 := by
    have hs : Parameters.lmExpansionOrder n + lm311GirthBudget n + 2 +
        4 * (3 * Parameters.lmRadius (1 / 1024) n + 1) +
        4 * Parameters.lmExpansionOrder n ≤
          Parameters.lmExpansionOrder n ^ 2 := by
      simpa only [lm311GirthBudget] using hstars.1
    have hroute : 3 * m + 1 ≤
        3 * Parameters.lmRadius (1 / 1024) n + 1 := by omega
    dsimp only [D, m]
    omega
  have hlowStar : D + lm311GirthBudget n + 2 + 4 * D ≤ D ^ 2 := by
    simpa only [D, lm311GirthBudget] using hstars.2
  refine
    { card_large := hn
      expansion_pos := hDpos
      local_radius := hlocalRadius
      local_fit := by simpa [ell, m] using hlocalFit
      carrier_base := by simpa [div, carrier, D] using hcarrierBase
      warm_large := by simpa [div, D] using hwarmLarge
      global_cost := by simpa [D] using hglobal
      packing := by simpa only [lm311GirthBudget] using hpacking
      reservoir_half := by simpa [D] using hhalf
      high_star := by simpa [D, m] using hhighStar
      low_star := by simpa [D] using hlowStar }

/-! ## The concrete source-Lemma-3.11 certificate -/

/-- Shared local/global rate argument for the four combined schedules in the
concrete Lemma 3.11 certificate.  Keeping this branch outside the record
constructor makes each certificate field a small arithmetic specialization. -/
private theorem lm311Combined_rate_of_scaleBounds
    {n d start i s cost : ℕ} (S : LM311ScaleBounds n)
    (hd : lm311DegreeThreshold ≤ d)
    (hstartCut : (d : ℝ) / 128 ≤ (start : ℝ))
    (hcombinedCut : (d : ℝ) / 128 ≤
      (lm311CombinedStart n start : ℝ))
    (hi : i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n)
    (hlocalCost : i < Parameters.lm311AdaptiveRounds n →
      cost ≤ lm311AdaptiveGain d (lm311AdaptiveCurve d start i))
    (hglobalCost : cost ≤ lm311GlobalCost n)
    (his : lm311CombinedGrowth n d start i ≤ s) (hsn : s ≤ n / 2) :
    ((((lm311CombinedGain n d start i + cost : ℕ) : ℝ)) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)) := by
  have hd1 : 1 ≤ d := (by norm_num [lm311DegreeThreshold] :
    1 ≤ lm311DegreeThreshold).trans hd
  by_cases hilocal : i < Parameters.lm311AdaptiveRounds n
  · rw [lm311CombinedGrowth, if_pos hilocal] at his
    rw [lm311CombinedGain, if_pos hilocal]
    exact lm311AdaptiveGain_add_cost_le_expansion hd1
      (hstartCut.trans (by exact_mod_cast
        lm311AdaptiveCurve_start_le d start i)) his (hlocalCost hilocal)
  · exact lm311CombinedGlobal_rate S.card_large hd1 (by omega) hcombinedCut
      (hglobalCost.trans S.global_cost) his hsn

private structure LM311RatePackage (n d : ℕ) where
  highRoot : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n, ∀ s : ℕ,
    lm311CombinedGrowth n d (lm311AdaptiveSeed d) i ≤ s → s ≤ n / 2 →
      ((((lm311CombinedGain n d (lm311AdaptiveSeed d) i +
        lm311HighFixedBudget 2 0 + (2 * (i + 2) + 1) + 2 ^ 2 * (i + 3) : ℕ) : ℝ)) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
  highHub : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n, ∀ s : ℕ,
    lm311CombinedGrowth n d (lm311CarrierStart n d) i ≤ s → s ≤ n / 2 →
      ((((lm311CombinedGain n d (lm311CarrierStart n d) i +
        lm311HighCarrierBudget n 2 0 (3 * lmGrowthRounds n + 1) : ℕ) : ℝ)) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
  reservoir : ∀ i < Parameters.lm311AdaptiveRounds n, ∀ s : ℕ,
    lm311AdaptiveCurve d (lm311AdaptiveSeed d) i ≤ s → s ≤ n / 2 →
      ((((lm311AdaptiveGain d (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i) +
        2 * 2 ^ 2 + 0 + 2 + (2 * (i + 2) + 1) : ℕ) : ℝ)) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
  lowRoot : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n, ∀ s : ℕ,
    lm311CombinedGrowth n d (lm311AdaptiveSeed d) i ≤ s → s ≤ n / 2 →
      ((((lm311CombinedGain n d (lm311AdaptiveSeed d) i + 4 * 2 ^ 2 +
        2 * 0 + 2 * 2 + (2 * (i + 2) + 1) + 2 ^ 2 * (i + 3) +
        (if i < Parameters.lm311LocalRadius n then 0
          else 2 ^ 2 * Parameters.lmExpansionOrder n ^ 2) : ℕ) : ℝ)) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
  lowReservoir : d - 1 ≤ Parameters.lmExpansionOrder n ^ 2 →
    ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n, ∀ s : ℕ,
    lm311CombinedGrowth n d (lm311CarrierStart n d) i ≤ s → s ≤ n / 2 →
      ((((lm311CombinedGain n d (lm311CarrierStart n d) i + 2 * 0 +
        2 * 2 ^ 2 + 2 * 2 + lm311GirthBudget n +
        2 ^ 2 * (3 * lmGrowthRounds n + 1) +
        (if i < Parameters.lm311LocalRadius n then 0
          else 2 ^ 2 * Parameters.lmExpansionOrder n ^ 2) : ℕ) : ℝ)) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))

private theorem lm311RatePackage_of_scaleBounds {n d : ℕ}
    (S : LM311ScaleBounds n) (hd : lm311DegreeThreshold ≤ d)
    (hcarrierStartN : lm311CarrierStart n d ≤ n) : LM311RatePackage n d := by
  have hd1 : 1 ≤ d := (by norm_num [lm311DegreeThreshold] :
    1 ≤ lm311DegreeThreshold).trans hd
  have hseedCut := lm311AdaptiveSeed_cutoff d
  have hcarrierSeed : lm311AdaptiveSeed d ≤ lm311CarrierStart n d := le_max_right _ _
  have hcarrierCut : (d : ℝ) / 128 ≤ (lm311CarrierStart n d : ℝ) :=
    hseedCut.trans (by exact_mod_cast hcarrierSeed)
  have hcombinedCutSeed : (d : ℝ) / 128 ≤
      (lm311CombinedStart n (lm311AdaptiveSeed d) : ℝ) :=
    hseedCut.trans (by exact_mod_cast
      (le_max_right (Parameters.lmExpansionOrder n ^ 4) (lm311AdaptiveSeed d)))
  have hcombinedCutCarrier : (d : ℝ) / 128 ≤
      (lm311CombinedStart n (lm311CarrierStart n d) : ℝ) :=
    hcarrierCut.trans (by exact_mod_cast
      (le_max_right (Parameters.lmExpansionOrder n ^ 4) (lm311CarrierStart n d)))
  refine
    { highRoot := ?_
      highHub := ?_
      reservoir := ?_
      lowRoot := ?_
      lowReservoir := ?_ }
  · intro i hi s his hsn
    let cost := lm311HighFixedBudget 2 0 + (2 * (i + 2) + 1) + 2 ^ 2 * (i + 3)
    have hlocalCost (_ : i < Parameters.lm311AdaptiveRounds n) :
        cost ≤ lm311AdaptiveGain d (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i) := by
      have hcost : cost ≤ 6 * i + 40 := by
        dsimp [cost, lm311HighFixedBudget]
        omega
      exact hcost.trans (lm311AdaptiveCost_le_gain (d := d) (i := i) hd)
    have hglobalCost : cost ≤ lm311GlobalCost n := by
      dsimp [cost, lm311HighFixedBudget, lm311GlobalCost, lm311CarrierCost] at hi ⊢
      omega
    simpa only [cost, Nat.add_assoc] using
      lm311Combined_rate_of_scaleBounds S hd hseedCut hcombinedCutSeed hi
        hlocalCost hglobalCost his hsn
  · intro i hi s his hsn
    let cost := lm311HighCarrierBudget n 2 0 (3 * lmGrowthRounds n + 1)
    have hbudget : cost ≤ lm311CarrierCost n := by
      dsimp [cost, lm311HighCarrierBudget, lm311HighFixedBudget, lm311CarrierCost]
      omega
    have hlocalCost (_ : i < Parameters.lm311AdaptiveRounds n) :
        cost ≤ lm311AdaptiveGain d (lm311AdaptiveCurve d (lm311CarrierStart n d) i) :=
      hbudget.trans (lm311CarrierCost_le_adaptiveGain_curve S.card_large hd1 hcarrierStartN)
    have hglobalCost : cost ≤ lm311GlobalCost n := by
      apply hbudget.trans
      dsimp [lm311GlobalCost, lm311CarrierCost]
      omega
    simpa only [cost] using
      lm311Combined_rate_of_scaleBounds S hd hcarrierCut hcombinedCutCarrier hi
        hlocalCost hglobalCost his hsn
  · intro i hi s his hsn
    have hcost : 2 * 2 ^ 2 + 0 + 2 + (2 * (i + 2) + 1) ≤ 6 * i + 40 := by omega
    have hcostGain : 2 * 2 ^ 2 + 0 + 2 + (2 * (i + 2) + 1) ≤
        lm311AdaptiveGain d (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i) :=
      hcost.trans (lm311AdaptiveCost_le_gain (d := d) (i := i) hd)
    simpa only [Nat.add_assoc] using
      lm311AdaptiveGain_add_cost_le_expansion hd1
        (hseedCut.trans (by exact_mod_cast
          lm311AdaptiveCurve_start_le d (lm311AdaptiveSeed d) i)) his hcostGain
  · intro i hi s his hsn
    let cost := 4 * 2 ^ 2 + 2 * 0 + 2 * 2 + (2 * (i + 2) + 1) +
      2 ^ 2 * (i + 3) + (if i < Parameters.lm311LocalRadius n then 0
        else 2 ^ 2 * Parameters.lmExpansionOrder n ^ 2)
    have hlocalCost (hilocal : i < Parameters.lm311AdaptiveRounds n) :
        cost ≤ lm311AdaptiveGain d (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i) := by
      have hiell : i < Parameters.lm311LocalRadius n := by
        have := S.local_radius
        omega
      have hcost : 4 * 2 ^ 2 + 2 * 0 + 2 * 2 + (2 * (i + 2) + 1) +
          2 ^ 2 * (i + 3) + 0 ≤ 6 * i + 40 := by omega
      simpa only [cost, if_pos hiell] using
        hcost.trans (lm311AdaptiveCost_le_gain (d := d) (i := i) hd)
    have hglobalCost : cost ≤ lm311GlobalCost n := by
      dsimp only [cost, lm311GlobalCost]
      by_cases hiell : i < Parameters.lm311LocalRadius n
      · rw [if_pos hiell]
        norm_num
        omega
      · rw [if_neg hiell]
        norm_num
        omega
    simpa only [cost, Nat.add_assoc] using
      lm311Combined_rate_of_scaleBounds S hd hseedCut hcombinedCutSeed hi
        hlocalCost hglobalCost his hsn
  · intro hdDelta i hi s his hsn
    let cost := 2 * 0 + 2 * 2 ^ 2 + 2 * 2 + lm311GirthBudget n +
      2 ^ 2 * (3 * lmGrowthRounds n + 1) +
        (if i < Parameters.lm311LocalRadius n then 0
          else 2 ^ 2 * Parameters.lmExpansionOrder n ^ 2)
    have hlocalCost (hilocal : i < Parameters.lm311AdaptiveRounds n) :
        cost ≤ lm311AdaptiveGain d (lm311AdaptiveCurve d (lm311CarrierStart n d) i) := by
      have hiell : i < Parameters.lm311LocalRadius n := by
        have := S.local_radius
        omega
      have hcost : 2 * 0 + 2 * 2 ^ 2 + 2 * 2 + lm311GirthBudget n +
          2 ^ 2 * (3 * lmGrowthRounds n + 1) + 0 ≤ lm311CarrierCost n := by
        dsimp [lm311CarrierCost]
        omega
      simpa only [cost, if_pos hiell] using
        hcost.trans (lm311CarrierCost_le_adaptiveGain_curve
          S.card_large hd1 hcarrierStartN)
    have hglobalCost : cost ≤ lm311GlobalCost n := by
      dsimp only [cost, lm311GlobalCost]
      by_cases hiell : i < Parameters.lm311LocalRadius n
      · rw [if_pos hiell]
        dsimp [lm311CarrierCost]
        norm_num
        omega
      · rw [if_neg hiell]
        dsimp [lm311CarrierCost]
        norm_num
        omega
    simpa only [cost, Nat.add_assoc] using
      lm311Combined_rate_of_scaleBounds S hd hcarrierCut hcombinedCutCarrier hi
        hlocalCost hglobalCost his hsn

private structure LM311CarrierFacts (n d : ℕ) where
  start_le_n : lm311CarrierStart n d ≤ n
  start_le_highHub : lm311CarrierStart n d ≤
    lm311HighHubSeed n d (Parameters.lmExpansionOrder n ^ 2) 2 0
      (3 * lmGrowthRounds n + 1)
  start_le_delta : d - 1 ≤ Parameters.lmExpansionOrder n ^ 2 →
    lm311CarrierStart n d ≤ Parameters.lmExpansionOrder n ^ 2

private theorem lm311CarrierFacts_of_scaleBounds {n d : ℕ}
    (S : LM311ScaleBounds n) (hd : lm311DegreeThreshold ≤ d) (hdn : d ≤ n) :
    LM311CarrierFacts n d := by
  let D := Parameters.lmExpansionOrder n
  let Delta := D ^ 2
  let m := lmGrowthRounds n
  let seed := lm311AdaptiveSeed d
  let carrier := lm311CarrierCost n
  let carrierStart := lm311CarrierStart n d
  have hn : 32 ≤ n := S.card_large
  have hDpos : 0 < D := by simpa [D] using S.expansion_pos
  have hDDelta : D ≤ Delta := by
    dsimp [Delta]
    nlinarith
  have hDeltaN : Delta ≤ n / 2 + 1 := by
    simpa [Delta, D] using S.reservoir_half
  have hD_le_n : D ≤ n := hDDelta.trans (hDeltaN.trans (by omega))
  have hseedLeD : 64 * seed ≤ d := by
    have hmod := Nat.mod_lt d (by norm_num : 0 < 128)
    have hdecomp := Nat.div_add_mod d 128
    dsimp [seed, lm311AdaptiveSeed]
    dsimp [lm311DegreeThreshold] at hd
    omega
  have hseedLeN : seed ≤ n := by
    have : seed ≤ d := by omega
    exact this.trans hdn
  have hcarrierBudget :
      lm311HighCarrierBudget n 2 0 (3 * m + 1) ≤ carrier := by
    dsimp [carrier, lm311CarrierCost, lm311HighCarrierBudget,
      lm311HighFixedBudget]
    omega
  have hcarrierTwice : 2 * (carrier + 1) ≤ D := by
    have hbase := S.carrier_base
    have hmul : 2 * (carrier + 1) ≤
        2 * lmGrowthDivisor n * (carrier + 1) := by
      calc
        2 * (carrier + 1) = 2 * 1 * (carrier + 1) := by ring
        _ ≤ 2 * lmGrowthDivisor n * (carrier + 1) := by
          gcongr
          exact Nat.succ_le_iff.2 (lmGrowthDivisor_pos (hn.trans' (by omega)))
    exact hmul.trans (by simpa [carrier, D] using hbase)
  have hcarrierLeD : carrier ≤ D := by omega
  have hcarrierBaseLeD :
      2 * lmGrowthDivisor n * (carrier + 1) ≤ D := by
    simpa [carrier, D] using S.carrier_base
  have hcarrierStartN : carrierStart ≤ n := by
    apply max_le
    · exact hcarrierBaseLeD.trans hD_le_n
    · exact hseedLeN
  have hcarrierStart_highHub : carrierStart ≤
      lm311HighHubSeed n d Delta 2 0 (3 * m + 1) := by
    let hubCost := lm311HighCarrierBudget n 2 0 (3 * m + 1)
    have hhubCarrier : hubCost ≤ carrier := by simpa [hubCost] using hcarrierBudget
    have hfiveD : 5 * D ≤ Delta := by
      have hstar := S.high_star
      change D + lm311GirthBudget n + 2 + 4 * (3 * m + 1) + 4 * D ≤
        Delta at hstar
      omega
    have hbaseHub :
        2 * lmGrowthDivisor n * (carrier + 1) + hubCost ≤ Delta := by
      have hhubD : hubCost ≤ D := hhubCarrier.trans hcarrierLeD
      have hsum : 2 * lmGrowthDivisor n * (carrier + 1) + hubCost ≤ D + D :=
        Nat.add_le_add hcarrierBaseLeD hhubD
      exact hsum.trans ((show D + D ≤ 5 * D by omega).trans hfiveD)
    have hseedHub : seed + hubCost ≤ max (d - 1) Delta := by
      by_cases hlow : d - 1 ≤ Delta
      · have hseedDelta : 64 * seed ≤ Delta + 1 := hseedLeD.trans (by omega)
        have htwoHub : 2 * hubCost ≤ D :=
          (Nat.mul_le_mul_left 2 hhubCarrier).trans (by omega)
        have : seed + hubCost ≤ Delta := by omega
        exact this.trans (le_max_right _ _)
      · have hDeltaD : Delta < d := by omega
        have h128D : 128 * D ≤ d := by
          by_cases hDlarge : 128 ≤ D
          · have hDD : 128 * D ≤ D ^ 2 := by
              simpa [pow_two, mul_comm] using Nat.mul_le_mul_right D hDlarge
            exact hDD.trans (by simpa [Delta] using hDeltaD.le)
          · have hdlarge : 2 ^ 60 ≤ d := hd
            omega
        have h128Hub : 128 * hubCost ≤ d := by
          have hhubD := hhubCarrier.trans hcarrierLeD
          exact (Nat.mul_le_mul_left 128 hhubD).trans h128D
        have : seed + hubCost ≤ d - 1 := by omega
        exact this.trans (le_max_left _ _)
    have hstartHub : carrierStart + hubCost ≤ max (d - 1) Delta := by
      dsimp [carrierStart, lm311CarrierStart]
      simpa only [max_add_add_right] using
        max_le (hbaseHub.trans (le_max_right _ _)) hseedHub
    dsimp [lm311HighHubSeed]
    exact Nat.le_sub_of_add_le hstartHub
  have hcarrierStartDelta (hdDelta : d - 1 ≤ Delta) : carrierStart ≤ Delta := by
    apply max_le
    · exact hcarrierBaseLeD.trans hDDelta
    · have : seed ≤ Delta := by omega
      exact this
  refine
    { start_le_n := by simpa [carrierStart] using hcarrierStartN
      start_le_highHub := by
        simpa [carrierStart, Delta, D, m] using hcarrierStart_highHub
      start_le_delta := by
        intro hdDelta
        apply hcarrierStartDelta
        simpa [Delta, D] using hdDelta }

private structure LM311SetupPackage (n d : ℕ) : Prop where
  ell_pos : 0 < Parameters.lm311LocalRadius n
  m_pos : 0 < lmGrowthRounds n
  local_pos : 0 < Parameters.lm311AdaptiveRounds n
  seed_sources :
    lm311AdaptiveSeed d ≤ lm311HighRootSeed d 2 0 ∧
      lm311AdaptiveSeed d ≤ lm311ReservoirSeed d 2 0 ∧
      lm311AdaptiveSeed d ≤ lm311LowRootSeed d 2 0
  carrier_start_n : lm311CarrierStart n d ≤ n
  carrier_high_hub : lm311CarrierStart n d ≤
    lm311HighHubSeed n d (Parameters.lmExpansionOrder n ^ 2) 2 0
      (3 * lmGrowthRounds n + 1)
  carrier_delta : d - 1 ≤ Parameters.lmExpansionOrder n ^ 2 →
    lm311CarrierStart n d ≤ Parameters.lmExpansionOrder n ^ 2

private theorem lm311SetupPackage_of_scaleBounds {n d : ℕ}
    (S : LM311ScaleBounds n) (hd : lm311DegreeThreshold ≤ d) (hdn : d ≤ n) :
    LM311SetupPackage n d := by
  let D := Parameters.lmExpansionOrder n
  let Delta := D ^ 2
  let ell := Parameters.lm311LocalRadius n
  let localRounds := Parameters.lm311AdaptiveRounds n
  let m := lmGrowthRounds n
  let seed := lm311AdaptiveSeed d
  let carrier := lm311CarrierCost n
  let carrierStart := lm311CarrierStart n d
  have hn : 32 ≤ n := S.card_large
  have hDpos : 0 < D := by simpa [D] using S.expansion_pos
  have hDDelta : D ≤ Delta := by
    dsimp [Delta]
    nlinarith
  have hDeltaN : Delta ≤ n / 2 + 1 := by simpa [Delta, D] using S.reservoir_half
  have hD_le_n : D ≤ n := hDDelta.trans (hDeltaN.trans (by omega))
  have hellpos : 0 < ell := by
    have := S.local_radius
    dsimp [ell, localRounds]
    omega
  have hmpos : 0 < m := by
    have := S.local_fit
    dsimp [ell, m]
    omega
  have hlocalpos : 0 < localRounds := by
    have hstages : 0 < Parameters.lm311AdaptiveStages n := by
      simp [Parameters.lm311AdaptiveStages]
    have hstrict := lm311AdaptiveTime_strictMono hstages
    simpa [localRounds, Parameters.lm311AdaptiveRounds,
      Parameters.lm311AdaptiveTime] using hstrict
  have hseedSources := lm311AdaptiveSeed_le_source_seeds hd
  /-
  have hseedLeD : 64 * seed ≤ d := by
    have hmod := Nat.mod_lt d (by norm_num : 0 < 128)
    have hdecomp := Nat.div_add_mod d 128
    dsimp [seed, lm311AdaptiveSeed]
    dsimp [lm311DegreeThreshold] at hd
    omega
  have hseedLeN : seed ≤ n := by
    have : seed ≤ d := by omega
    exact this.trans hdn
  have hcarrierBudget :
      lm311HighCarrierBudget n 2 0 (3 * m + 1) ≤ carrier := by
    dsimp [carrier, lm311CarrierCost, lm311HighCarrierBudget,
      lm311HighFixedBudget]
    omega
  have hdivpos : 0 < lmGrowthDivisor n :=
    lmGrowthDivisor_pos (hn.trans' (by omega))
  have hcarrierTwice : 2 * (carrier + 1) ≤ D := by
    have hmul : 2 * (carrier + 1) ≤
        2 * lmGrowthDivisor n * (carrier + 1) := by
      calc
        2 * (carrier + 1) = 2 * 1 * (carrier + 1) := by ring
        _ ≤ 2 * lmGrowthDivisor n * (carrier + 1) := by
          gcongr
          omega
    exact hmul.trans (by simpa [carrier, D] using S.carrier_base)
  have hcarrierLeD : carrier ≤ D := by omega
  have hcarrierBaseLeD :
      2 * lmGrowthDivisor n * (carrier + 1) ≤ D := by
    simpa [carrier, D] using S.carrier_base
  have hcarrierStartN : carrierStart ≤ n := by
    apply max_le
    · exact hcarrierBaseLeD.trans hD_le_n
    · exact hseedLeN
  have hcarrierStartHighHub : carrierStart ≤
      lm311HighHubSeed n d Delta 2 0 (3 * m + 1) := by
    let hubCost := lm311HighCarrierBudget n 2 0 (3 * m + 1)
    have hhubCarrier : hubCost ≤ carrier := by simpa [hubCost] using hcarrierBudget
    have hfiveD : 5 * D ≤ Delta := by
      have hstar := S.high_star
      change D + lm311GirthBudget n + 2 + 4 * (3 * m + 1) + 4 * D ≤
        Delta at hstar
      omega
    have hbaseHub :
        2 * lmGrowthDivisor n * (carrier + 1) + hubCost ≤ Delta := by
      have htwoHub : 2 * hubCost ≤ D :=
        (Nat.mul_le_mul_left 2 hhubCarrier).trans (by omega)
      omega
    have hseedHub : seed + hubCost ≤ max (d - 1) Delta := by
      by_cases hlow : d - 1 ≤ Delta
      · have hseedDelta : 64 * seed ≤ Delta + 1 := hseedLeD.trans (by omega)
        have htwoHub : 2 * hubCost ≤ D :=
          (Nat.mul_le_mul_left 2 hhubCarrier).trans (by omega)
        have : seed + hubCost ≤ Delta := by omega
        exact this.trans (le_max_right _ _)
      · have hDeltaD : Delta < d := by omega
        have h128D : 128 * D ≤ d := by
          by_cases hDlarge : 128 ≤ D
          · have hDD : 128 * D ≤ D ^ 2 := by
              simpa [pow_two, mul_comm] using Nat.mul_le_mul_right D hDlarge
            exact hDD.trans (by simpa [Delta] using hDeltaD.le)
          · have hdlarge : 2 ^ 60 ≤ d := hd
            omega
        have h128Hub : 128 * hubCost ≤ d := by
          have hhubD := hhubCarrier.trans hcarrierLeD
          exact (Nat.mul_le_mul_left 128 hhubD).trans h128D
        have : seed + hubCost ≤ d - 1 := by omega
        exact this.trans (le_max_left _ _)
    have hstartHub : carrierStart + hubCost ≤ max (d - 1) Delta := by
      dsimp [carrierStart, lm311CarrierStart]
      simpa only [max_add_add_right] using
        max_le (hbaseHub.trans (le_max_right _ _)) hseedHub
    dsimp [lm311HighHubSeed]
    exact Nat.le_sub_of_add_le hstartHub
  have hcarrierStartDelta (hdDelta : d - 1 ≤ Delta) : carrierStart ≤ Delta := by
    apply max_le
    · exact hcarrierBaseLeD.trans hDDelta
    · omega
  -/
  have facts : LM311CarrierFacts n d := lm311CarrierFacts_of_scaleBounds S hd hdn
  exact
    { ell_pos := by simpa [ell] using hellpos
      m_pos := by simpa [m] using hmpos
      local_pos := by simpa [localRounds] using hlocalpos
      seed_sources := by simpa [seed] using hseedSources
      carrier_start_n := facts.start_le_n
      carrier_high_hub := by
        simpa [Delta, D, m] using facts.start_le_highHub
      carrier_delta := facts.start_le_delta }

private structure LM311GeometryPackage (n d : ℕ) : Prop where
  high_root_start : lm311CombinedGrowth n d (lm311AdaptiveSeed d) 0 ≤
    lm311HighRootSeed d 2 0
  high_hub_start : lm311CombinedGrowth n d (lm311CarrierStart n d) 0 ≤
    lm311HighHubSeed n d (Parameters.lmExpansionOrder n ^ 2) 2 0
      (3 * lmGrowthRounds n + 1)
  high_root_next : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    lm311CombinedGrowth n d (lm311AdaptiveSeed d) (i + 1) ≤
      lm311CombinedGrowth n d (lm311AdaptiveSeed d) i +
        lm311CombinedGain n d (lm311AdaptiveSeed d) i
  high_hub_next : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    lm311CombinedGrowth n d (lm311CarrierStart n d) (i + 1) ≤
      lm311CombinedGrowth n d (lm311CarrierStart n d) i +
        lm311CombinedGain n d (lm311CarrierStart n d) i
  high_root_lower : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    ((1 / 64) * (d : ℝ)) / 2 ≤
      (lm311CombinedGrowth n d (lm311AdaptiveSeed d) i : ℝ)
  high_hub_lower : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    ((1 / 64) * (d : ℝ)) / 2 ≤
      (lm311CombinedGrowth n d (lm311CarrierStart n d) i : ℝ)
  high_root_half : n / 2 + 1 ≤ lm311CombinedGrowth n d (lm311AdaptiveSeed d)
    (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n)
  high_hub_half : n / 2 + 1 ≤ lm311CombinedGrowth n d (lm311CarrierStart n d)
    (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n)
  high_connector : 2 * (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n + 1) <
    3 * lmGrowthRounds n + 1
  low_root_start : lm311CombinedGrowth n d (lm311AdaptiveSeed d) 0 ≤
    lm311LowRootSeed d 2 0
  reservoir_lower : ∀ i < Parameters.lm311AdaptiveRounds n,
    ((1 / 64) * (d : ℝ)) / 2 ≤
      (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i : ℝ)
  reservoir_target : Parameters.lmExpansionOrder n ^ 2 ≤
    lm311AdaptiveCurve d (lm311AdaptiveSeed d) (Parameters.lm311AdaptiveRounds n)
  low_reservoir_start :
    (if d - 1 ≤ Parameters.lmExpansionOrder n ^ 2 then
      lm311CombinedGrowth n d (lm311CarrierStart n d) else fun _ ↦ 0) 0 ≤
      Parameters.lmExpansionOrder n ^ 2
  low_reservoir_next : d - 1 ≤ Parameters.lmExpansionOrder n ^ 2 →
    ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
      (if d - 1 ≤ Parameters.lmExpansionOrder n ^ 2 then
        lm311CombinedGrowth n d (lm311CarrierStart n d) else fun _ ↦ 0) (i + 1) ≤
      (if d - 1 ≤ Parameters.lmExpansionOrder n ^ 2 then
        lm311CombinedGrowth n d (lm311CarrierStart n d) else fun _ ↦ 0) i +
      (if d - 1 ≤ Parameters.lmExpansionOrder n ^ 2 then
        lm311CombinedGain n d (lm311CarrierStart n d) else fun _ ↦ 0) i
  low_reservoir_lower : d - 1 ≤ Parameters.lmExpansionOrder n ^ 2 →
    ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
      ((1 / 64) * (d : ℝ)) / 2 ≤
      ((if d - 1 ≤ Parameters.lmExpansionOrder n ^ 2 then
        lm311CombinedGrowth n d (lm311CarrierStart n d) else fun _ ↦ 0) i : ℝ)
  low_reservoir_half : d - 1 ≤ Parameters.lmExpansionOrder n ^ 2 →
    n / 2 + 1 ≤
      (if d - 1 ≤ Parameters.lmExpansionOrder n ^ 2 then
        lm311CombinedGrowth n d (lm311CarrierStart n d) else fun _ ↦ 0)
          (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n)
  low_connector : 2 * (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n) + 1 <
    3 * lmGrowthRounds n + 1
  attach_radius : 3 * lmGrowthRounds n + 2 * Parameters.lm311LocalRadius n ≤
    5 * lmGrowthRounds n

private theorem lm311GeometryPackage_of_scaleBounds {n d : ℕ}
    (S : LM311ScaleBounds n) (hd : lm311DegreeThreshold ≤ d)
    (setup : LM311SetupPackage n d) : LM311GeometryPackage n d := by
  have hlocalpos := setup.local_pos
  have hseedCut := lm311AdaptiveSeed_cutoff d
  have hcarrierSeed : lm311AdaptiveSeed d ≤ lm311CarrierStart n d := le_max_right _ _
  have hcarrierCut : (d : ℝ) / 128 ≤ (lm311CarrierStart n d : ℝ) :=
    hseedCut.trans (by exact_mod_cast hcarrierSeed)
  have hwarmSeed : 2 * lmGrowthDivisor n ≤
      lm311CombinedStart n (lm311AdaptiveSeed d) :=
    S.warm_large.trans (le_max_left _ _)
  have hwarmCarrier : 2 * lmGrowthDivisor n ≤
      lm311CombinedStart n (lm311CarrierStart n d) :=
    S.warm_large.trans (le_max_left _ _)
  refine
    { high_root_start := by
        rw [lm311CombinedGrowth_zero hlocalpos]
        exact setup.seed_sources.1
      high_hub_start := by
        rw [lm311CombinedGrowth_zero hlocalpos]
        exact setup.carrier_high_hub
      high_root_next := by
        intro i hi
        exact lm311Combined_next hd S.expansion_pos le_rfl
      high_hub_next := by
        intro i hi
        exact lm311Combined_next hd S.expansion_pos hcarrierSeed
      high_root_lower := by
        intro i hi
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hseedCut
      high_hub_lower := by
        intro i hi
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hcarrierCut
      high_root_half := lm311Combined_half S.card_large hwarmSeed
      high_hub_half := lm311Combined_half S.card_large hwarmCarrier
      high_connector := by
        have hlocal := S.local_radius
        have hfit := S.local_fit
        omega
      low_root_start := by
        rw [lm311CombinedGrowth_zero hlocalpos]
        exact setup.seed_sources.2.2
      reservoir_lower := by
        intro i hi
        have hcurveReal : (lm311AdaptiveSeed d : ℝ) ≤
            (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i : ℝ) := by
          exact_mod_cast lm311AdaptiveCurve_start_le d (lm311AdaptiveSeed d) i
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact hseedCut.trans hcurveReal
      reservoir_target := by
        have hwarm := lm311AdaptiveCurve_reaches_warmTarget
          (n := n) (d := d) hd S.expansion_pos
        have hDone : 1 ≤ Parameters.lmExpansionOrder n :=
          Nat.succ_le_iff.2 S.expansion_pos
        have hsq : Parameters.lmExpansionOrder n ^ 2 ≤
            Parameters.lmExpansionOrder n ^ 4 :=
          pow_le_pow_right₀ hDone (by omega)
        exact hsq.trans hwarm
      low_reservoir_start := by
        by_cases hcase : d - 1 ≤ Parameters.lmExpansionOrder n ^ 2
        · rw [if_pos hcase, lm311CombinedGrowth_zero hlocalpos]
          exact setup.carrier_delta hcase
        · simp [hcase]
      low_reservoir_next := by
        intro hcase i hi
        rw [if_pos hcase, if_pos hcase]
        exact lm311Combined_next hd S.expansion_pos hcarrierSeed
      low_reservoir_lower := by
        intro hcase i hi
        rw [if_pos hcase]
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hcarrierCut
      low_reservoir_half := by
        intro hcase
        rw [if_pos hcase]
        exact lm311Combined_half S.card_large hwarmCarrier
      low_connector := by
        have hlocal := S.local_radius
        have hfit := S.local_fit
        omega
      attach_radius := by
        have hfit := S.local_fit
        omega }

private structure LM311HighPackage (n d : ℕ) : Prop where
  root_start : lm311CombinedGrowth n d (lm311AdaptiveSeed d) 0 ≤
    lm311HighRootSeed d 2 0
  hub_start : lm311CombinedGrowth n d (lm311CarrierStart n d) 0 ≤
    lm311HighHubSeed n d (Parameters.lmExpansionOrder n ^ 2) 2 0
      (3 * lmGrowthRounds n + 1)
  root_next : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    lm311CombinedGrowth n d (lm311AdaptiveSeed d) (i + 1) ≤
      lm311CombinedGrowth n d (lm311AdaptiveSeed d) i +
        lm311CombinedGain n d (lm311AdaptiveSeed d) i
  hub_next : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    lm311CombinedGrowth n d (lm311CarrierStart n d) (i + 1) ≤
      lm311CombinedGrowth n d (lm311CarrierStart n d) i +
        lm311CombinedGain n d (lm311CarrierStart n d) i
  root_lower : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    ((1 / 64) * (d : ℝ)) / 2 ≤
      (lm311CombinedGrowth n d (lm311AdaptiveSeed d) i : ℝ)
  hub_lower : ∀ i < Parameters.lm311AdaptiveRounds n + lmGrowthRounds n,
    ((1 / 64) * (d : ℝ)) / 2 ≤
      (lm311CombinedGrowth n d (lm311CarrierStart n d) i : ℝ)
  root_half : n / 2 + 1 ≤ lm311CombinedGrowth n d (lm311AdaptiveSeed d)
    (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n)
  hub_half : n / 2 + 1 ≤ lm311CombinedGrowth n d (lm311CarrierStart n d)
    (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n)
  high_connector : 2 * (Parameters.lm311AdaptiveRounds n + lmGrowthRounds n + 1) <
    3 * lmGrowthRounds n + 1
  reservoir_lower : ∀ i < Parameters.lm311AdaptiveRounds n,
    ((1 / 64) * (d : ℝ)) / 2 ≤
      (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i : ℝ)
  reservoir_target : Parameters.lmExpansionOrder n ^ 2 ≤
    lm311AdaptiveCurve d (lm311AdaptiveSeed d) (Parameters.lm311AdaptiveRounds n)

private theorem lm311HighPackage_of_packages {n d : ℕ}
    (S : LM311ScaleBounds n) (hd : lm311DegreeThreshold ≤ d)
    (setup : LM311SetupPackage n d) : LM311HighPackage n d := by
  have hseedCut := lm311AdaptiveSeed_cutoff d
  have hcarrierSeed : lm311AdaptiveSeed d ≤ lm311CarrierStart n d := le_max_right _ _
  have hcarrierCut : (d : ℝ) / 128 ≤ (lm311CarrierStart n d : ℝ) :=
    hseedCut.trans (by exact_mod_cast hcarrierSeed)
  have hlocalpos := setup.local_pos
  have hwarmSeed : 2 * lmGrowthDivisor n ≤
      lm311CombinedStart n (lm311AdaptiveSeed d) :=
    S.warm_large.trans (le_max_left _ _)
  have hwarmCarrier : 2 * lmGrowthDivisor n ≤
      lm311CombinedStart n (lm311CarrierStart n d) :=
    S.warm_large.trans (le_max_left _ _)
  refine
    { root_start := by
        rw [lm311CombinedGrowth_zero hlocalpos]
        exact setup.seed_sources.1
      hub_start := by
        rw [lm311CombinedGrowth_zero hlocalpos]
        exact setup.carrier_high_hub
      root_next := by
        intro i hi
        apply lm311Combined_next hd S.expansion_pos
        rfl
      hub_next := fun i _ ↦ lm311Combined_next hd S.expansion_pos hcarrierSeed
      root_lower := by
        intro i hi
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hseedCut
      hub_lower := by
        intro i hi
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hcarrierCut
      root_half := lm311Combined_half S.card_large hwarmSeed
      hub_half := lm311Combined_half S.card_large hwarmCarrier
      high_connector := by
        have hlocal := S.local_radius
        have hfit := S.local_fit
        omega
      reservoir_lower := by
        intro i hi
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact hseedCut.trans (by exact_mod_cast
          lm311AdaptiveCurve_start_le d (lm311AdaptiveSeed d) i)
      reservoir_target := by
        have hwarm := lm311AdaptiveCurve_reaches_warmTarget
          (n := n) (d := d) hd S.expansion_pos
        have hDone : 1 ≤ Parameters.lmExpansionOrder n :=
          Nat.succ_le_iff.2 S.expansion_pos
        have hsq : Parameters.lmExpansionOrder n ^ 2 ≤
            Parameters.lmExpansionOrder n ^ 4 :=
          pow_le_pow_right₀ hDone (by omega)
        exact hsq.trans hwarm }

private noncomputable def lm311Numerics_of_packages {n d : ℕ}
    (S : LM311ScaleBounds n) (hd : lm311DegreeThreshold ≤ d)
    (setup : LM311SetupPackage n d) (rates : LM311RatePackage n d)
    (geom : LM311GeometryPackage n d) :
    LM311Numerics (1 / 1024) ((1 / 64) * (d : ℝ)) n 2 d
      (Parameters.lmExpansionOrder n) (Parameters.lmExpansionOrder n ^ 2)
      (Parameters.lm311LocalRadius n) (lmGrowthRounds n) 0 := by
  exact
    { k_pos := by omega
      four_le_d := (by norm_num [lm311DegreeThreshold] :
        4 ≤ lm311DegreeThreshold).trans hd
      D_pos := S.expansion_pos
      ell₀_pos := setup.ell_pos
      m_pos := setup.m_pos
      Delta_eq := rfl
      highRounds := Parameters.lm311AdaptiveRounds n + lmGrowthRounds n
      highRootGrowth := lm311CombinedGrowth n d (lm311AdaptiveSeed d)
      highRootGain := lm311CombinedGain n d (lm311AdaptiveSeed d)
      highHubGrowth := lm311CombinedGrowth n d (lm311CarrierStart n d)
      highHubGain := lm311CombinedGain n d (lm311CarrierStart n d)
      high_root_start := geom.high_root_start
      high_hub_start := geom.high_hub_start
      high_root_next := geom.high_root_next
      high_hub_next := geom.high_hub_next
      high_root_lower := geom.high_root_lower
      high_hub_lower := geom.high_hub_lower
      high_root_rate := rates.highRoot
      high_hub_rate := rates.highHub
      high_root_half := geom.high_root_half
      high_hub_half := geom.high_hub_half
      high_connector := geom.high_connector
      high_star_budget := S.high_star
      packing := S.packing
      reservoirRounds := Parameters.lm311AdaptiveRounds n
      reservoirGrowth := lm311AdaptiveCurve d (lm311AdaptiveSeed d)
      reservoirGain := fun i ↦
        lm311AdaptiveGain d (lm311AdaptiveCurve d (lm311AdaptiveSeed d) i)
      reservoir_radius := S.local_radius
      reservoir_start := setup.seed_sources.2.1
      reservoir_next := by
        intro i hi
        exact (lm311AdaptiveCurve_succ d (lm311AdaptiveSeed d) i).le
      reservoir_seed_lower := geom.reservoir_lower
      reservoir_rate := rates.reservoir
      reservoir_target := geom.reservoir_target
      reservoir_half := S.reservoir_half
      connectRounds := Parameters.lm311AdaptiveRounds n + lmGrowthRounds n
      lowRootGrowth := lm311CombinedGrowth n d (lm311AdaptiveSeed d)
      lowRootGain := lm311CombinedGain n d (lm311AdaptiveSeed d)
      lowReservoirGrowth :=
        if d - 1 ≤ Parameters.lmExpansionOrder n ^ 2 then
          lm311CombinedGrowth n d (lm311CarrierStart n d) else fun _ ↦ 0
      lowReservoirGain :=
        if d - 1 ≤ Parameters.lmExpansionOrder n ^ 2 then
          lm311CombinedGain n d (lm311CarrierStart n d) else fun _ ↦ 0
      low_root_start := geom.low_root_start
      low_reservoir_start := geom.low_reservoir_start
      low_root_next := geom.high_root_next
      low_reservoir_next := geom.low_reservoir_next
      low_root_lower := geom.high_root_lower
      low_reservoir_lower := geom.low_reservoir_lower
      low_root_rate := rates.lowRoot
      low_reservoir_rate := by
        intro hdDelta
        rw [if_pos hdDelta, if_pos hdDelta]
        exact rates.lowReservoir hdDelta
      low_root_half := geom.high_root_half
      low_reservoir_half := geom.low_reservoir_half
      low_connector := geom.low_connector
      attach_radius := geom.attach_radius
      low_star_budget := S.low_star }
  /-
  let D := Parameters.lmExpansionOrder n
  let Delta := D ^ 2
  let ell := Parameters.lm311LocalRadius n
  let localRounds := Parameters.lm311AdaptiveRounds n
  let m := lmGrowthRounds n
  let rounds := localRounds + m
  let seed := lm311AdaptiveSeed d
  let carrierStart := lm311CarrierStart n d
  have hn : 32 ≤ n := S.card_large
  have hd4 : 4 ≤ d := (by norm_num [lm311DegreeThreshold] :
    4 ≤ lm311DegreeThreshold).trans hd
  have hlocalpos : 0 < localRounds := by simpa [localRounds] using setup.local_pos
  have hseedCut : (d : ℝ) / 128 ≤ (seed : ℝ) := by
    simpa [seed] using lm311AdaptiveSeed_cutoff d
  have hcarrierSeed : seed ≤ carrierStart := by
    dsimp [seed, carrierStart, lm311CarrierStart]
    exact le_max_right _ _
  have hcarrierCut : (d : ℝ) / 128 ≤ (carrierStart : ℝ) :=
    hseedCut.trans (by exact_mod_cast hcarrierSeed)
  have hcarrierStart_highHub : carrierStart ≤
      lm311HighHubSeed n d Delta 2 0 (3 * m + 1) := by
    simpa [carrierStart, Delta, D, m] using setup.carrier_high_hub
  have hcarrierStartDelta (hdDelta : d - 1 ≤ Delta) : carrierStart ≤ Delta := by
    have h := setup.carrier_delta (by simpa [Delta, D] using hdDelta)
    simpa [carrierStart, Delta, D] using h
  have hcombinedWarmSeed : 2 * lmGrowthDivisor n ≤ lm311CombinedStart n seed :=
    S.warm_large.trans (le_max_left _ _)
  have hcombinedWarmCarrier :
      2 * lmGrowthDivisor n ≤ lm311CombinedStart n carrierStart :=
    S.warm_large.trans (le_max_left _ _)
  have high : LM311HighPackage n d := lm311HighPackage_of_packages S hd setup
  refine
    { k_pos := by omega
      four_le_d := hd4
      D_pos := S.expansion_pos
      ell₀_pos := setup.ell_pos
      m_pos := setup.m_pos
      Delta_eq := rfl
      highRounds := rounds
      highRootGrowth := lm311CombinedGrowth n d seed
      highRootGain := lm311CombinedGain n d seed
      highHubGrowth := lm311CombinedGrowth n d carrierStart
      highHubGain := lm311CombinedGain n d carrierStart
      high_root_start := high.root_start
      high_hub_start := high.hub_start
      high_root_next := high.root_next
      high_hub_next := high.hub_next
      high_root_lower := high.root_lower
      high_hub_lower := high.hub_lower
      high_root_rate := by simpa [rounds, seed] using rates.highRoot
      high_hub_rate := by simpa [rounds, carrierStart, m] using rates.highHub
      high_root_half := high.root_half
      high_hub_half := high.hub_half
      high_connector := high.high_connector
      high_star_budget := S.high_star
      packing := S.packing
      reservoirRounds := localRounds
      reservoirGrowth := lm311AdaptiveCurve d seed
      reservoirGain := fun i ↦ lm311AdaptiveGain d (lm311AdaptiveCurve d seed i)
      reservoir_radius := S.local_radius
      reservoir_start := by simpa [seed] using setup.seed_sources.2.1
      reservoir_next := by intro i hi; exact (lm311AdaptiveCurve_succ d seed i).le
      reservoir_seed_lower := high.reservoir_lower
      reservoir_rate := by simpa [localRounds, seed] using rates.reservoir
      reservoir_target := high.reservoir_target
      reservoir_half := S.reservoir_half
      connectRounds := rounds
      lowRootGrowth := lm311CombinedGrowth n d seed
      lowRootGain := lm311CombinedGain n d seed
      lowReservoirGrowth := if d - 1 ≤ Delta then
        lm311CombinedGrowth n d carrierStart else fun _ ↦ 0
      lowReservoirGain := if d - 1 ≤ Delta then
        lm311CombinedGain n d carrierStart else fun _ ↦ 0
      low_root_start := by
        rw [lm311CombinedGrowth_zero hlocalpos]
        exact setup.seed_sources.2.2
      low_reservoir_start := by
        by_cases hcase : d - 1 ≤ Delta
        · simp only [hcase, if_pos, lm311CombinedGrowth_zero hlocalpos]
          exact hcarrierStartDelta hcase
        · simp [hcase]
      low_root_next := by
        intro i hi
        apply lm311Combined_next hd S.expansion_pos
        rfl
      low_reservoir_next := by
        intro hdDelta i hi
        have hdLocal : d - 1 ≤ Delta := by simpa [Delta, D] using hdDelta
        rw [if_pos hdLocal, if_pos hdLocal]
        exact lm311Combined_next hd S.expansion_pos hcarrierSeed
      low_root_lower := by
        intro i hi
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hseedCut
      low_reservoir_lower := by
        intro hdDelta i hi
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hcarrierCut
      low_root_rate := by simpa [rounds, seed, ell, Delta, D] using rates.lowRoot
      low_reservoir_rate := by
        intro hdDelta
        simpa [rounds, carrierStart, ell, Delta, D, m] using
          rates.lowReservoir hdDelta
      low_root_half := by
        simpa [rounds, seed] using lm311Combined_half hn hcombinedWarmSeed
      low_reservoir_half := by
        intro hdDelta
        simpa [rounds, carrierStart] using lm311Combined_half hn hcombinedWarmCarrier
      low_connector := by
        have hlocal := S.local_radius
        have hfit := S.local_fit
        dsimp [rounds, localRounds, ell, m] at hlocal hfit ⊢
        omega
      attach_radius := by
        have hfit : 3 * ell + 2 ≤ m := by simpa [ell, m] using S.local_fit
        omega
      low_star_budget := S.low_star }
  -/

/-- The variable local/global schedules above instantiate every numerical
field of source Lemma 3.11.  This is uniform in the entire range `d ≤ n`;
large degree is handled by the adaptive exact-profile prefix, rather than by
a comparison between `d` and the polylogarithmic expansion order. -/
theorem lm311NumericsOfScaleBounds {n d : ℕ}
    (S : LM311ScaleBounds n) (hd : lm311DegreeThreshold ≤ d) (hdn : d ≤ n) :
    Nonempty (LM311Numerics (1 / 1024) ((1 / 64) * (d : ℝ)) n 2 d
      (Parameters.lmExpansionOrder n) (Parameters.lmExpansionOrder n ^ 2)
      (Parameters.lm311LocalRadius n) (lmGrowthRounds n) 0) := by
  let setup := lm311SetupPackage_of_scaleBounds S hd hdn
  let rates := lm311RatePackage_of_scaleBounds S hd setup.carrier_start_n
  let geom := lm311GeometryPackage_of_scaleBounds S hd setup
  exact ⟨lm311Numerics_of_packages S hd setup rates geom⟩
  /-
  let D := Parameters.lmExpansionOrder n
  let Delta := D ^ 2
  let ell := Parameters.lm311LocalRadius n
  let localRounds := Parameters.lm311AdaptiveRounds n
  let m := lmGrowthRounds n
  let rounds := localRounds + m
  let seed := lm311AdaptiveSeed d
  let carrier := lm311CarrierCost n
  let carrierStart := lm311CarrierStart n d
  have hn : 32 ≤ n := S.card_large
  have hd1 : 1 ≤ d := (by norm_num [lm311DegreeThreshold] :
    1 ≤ lm311DegreeThreshold).trans hd
  have hd4 : 4 ≤ d := (by norm_num [lm311DegreeThreshold] :
    4 ≤ lm311DegreeThreshold).trans hd
  /-
  have hDpos : 0 < D := by simpa [D] using S.expansion_pos
  have hDone : 1 ≤ D := hDpos
  have hDDelta : D ≤ Delta := by
    dsimp [Delta]
    nlinarith
  have hDeltaN : Delta ≤ n / 2 + 1 := by simpa [Delta, D] using S.reservoir_half
  have hDelta_le_n : Delta ≤ n := hDeltaN.trans (by omega)
  have hD_le_n : D ≤ n := hDDelta.trans hDelta_le_n
  have hellpos : 0 < ell := by
    have := S.local_radius
    dsimp [ell, localRounds]
    omega
  have hmpos : 0 < m := by
    have := S.local_fit
    dsimp [ell, m]
    omega
  have hdivpos : 0 < lmGrowthDivisor n :=
    lmGrowthDivisor_pos (hn.trans' (by omega))
  have hlocalpos : 0 < localRounds := by
    have hstages : 0 < Parameters.lm311AdaptiveStages n := by
      simp [Parameters.lm311AdaptiveStages]
    have hstrict := lm311AdaptiveTime_strictMono hstages
    simpa [localRounds, Parameters.lm311AdaptiveRounds,
      Parameters.lm311AdaptiveTime] using hstrict
  have hseedSources := lm311AdaptiveSeed_le_source_seeds hd
  have hseedCut : (d : ℝ) / 128 ≤ (seed : ℝ) := by
    simpa [seed] using lm311AdaptiveSeed_cutoff d
  have hseedLeD : 64 * seed ≤ d := by
    have hmod := Nat.mod_lt d (by norm_num : 0 < 128)
    have hdecomp := Nat.div_add_mod d 128
    dsimp [seed, lm311AdaptiveSeed]
    dsimp [lm311DegreeThreshold] at hd
    omega
  have hseedLeN : seed ≤ n := by
    have : seed ≤ d := by omega
    exact this.trans hdn
  have hcarrierBudget :
      lm311HighCarrierBudget n 2 0 (3 * m + 1) ≤ carrier := by
    dsimp [carrier, lm311CarrierCost, lm311HighCarrierBudget,
      lm311HighFixedBudget]
    omega
  have hcarrierTwice : 2 * (carrier + 1) ≤ D := by
    have hbase := S.carrier_base
    have hmul : 2 * (carrier + 1) ≤
        2 * lmGrowthDivisor n * (carrier + 1) := by
      calc
        2 * (carrier + 1) = 2 * 1 * (carrier + 1) := by ring
        _ ≤ 2 * lmGrowthDivisor n * (carrier + 1) := by
          gcongr
          omega
    exact hmul.trans (by simpa [carrier, D] using hbase)
  have hcarrierLeD : carrier ≤ D := by omega
  have hcarrierBaseLeD :
      2 * lmGrowthDivisor n * (carrier + 1) ≤ D := by
    simpa [carrier, D] using S.carrier_base
  have hcarrierStartN : carrierStart ≤ n := by
    apply max_le
    · exact hcarrierBaseLeD.trans hD_le_n
    · exact hseedLeN
  have hcarrierSeed : seed ≤ carrierStart := by
    exact le_max_right _ _
  have hcarrierCut : (d : ℝ) / 128 ≤ (carrierStart : ℝ) :=
    hseedCut.trans (by exact_mod_cast hcarrierSeed)
  have hcarrierStart_highHub : carrierStart ≤
      lm311HighHubSeed n d Delta 2 0 (3 * m + 1) := by
    let hubCost := lm311HighCarrierBudget n 2 0 (3 * m + 1)
    have hhubCarrier : hubCost ≤ carrier := by simpa [hubCost] using hcarrierBudget
    have hfiveD : 5 * D ≤ Delta := by
      have hstar := S.high_star
      change D + lm311GirthBudget n + 2 + 4 * (3 * m + 1) + 4 * D ≤
        Delta at hstar
      omega
    have hbaseHub :
        2 * lmGrowthDivisor n * (carrier + 1) + hubCost ≤ Delta := by
      have hbaseD := hcarrierBaseLeD
      have htwoHub : 2 * hubCost ≤ D := by
        exact (Nat.mul_le_mul_left 2 hhubCarrier).trans (by omega)
      omega
    have hseedHub : seed + hubCost ≤ max (d - 1) Delta := by
      by_cases hlow : d - 1 ≤ Delta
      · have hseedDelta : 64 * seed ≤ Delta + 1 := hseedLeD.trans (by omega)
        have htwoHub : 2 * hubCost ≤ D :=
          (Nat.mul_le_mul_left 2 hhubCarrier).trans (by omega)
        have : seed + hubCost ≤ Delta := by omega
        exact this.trans (le_max_right _ _)
      · have hDeltaD : Delta < d := by omega
        have h128D : 128 * D ≤ d := by
          by_cases hDlarge : 128 ≤ D
          · have hDD : 128 * D ≤ D ^ 2 := by
              simpa [pow_two, mul_comm] using Nat.mul_le_mul_right D hDlarge
            exact hDD.trans (by simpa [Delta] using hDeltaD.le)
          · have hdlarge : 2 ^ 60 ≤ d := hd
            omega
        have h128Hub : 128 * hubCost ≤ d := by
          have hhubD := hhubCarrier.trans hcarrierLeD
          exact (Nat.mul_le_mul_left 128 hhubD).trans h128D
        have : seed + hubCost ≤ d - 1 := by omega
        exact this.trans (le_max_left _ _)
    have hstartHub : carrierStart + hubCost ≤ max (d - 1) Delta := by
      dsimp [carrierStart, lm311CarrierStart]
      simpa only [max_add_add_right] using
        max_le (hbaseHub.trans (le_max_right _ _)) hseedHub
    dsimp [lm311HighHubSeed]
    exact (Nat.le_sub_of_add_le hstartHub)
  have hcarrierStartDelta (hdDelta : d - 1 ≤ Delta) : carrierStart ≤ Delta := by
    apply max_le
    · exact hcarrierBaseLeD.trans hDDelta
    · have : seed ≤ Delta := by omega
      exact this
  have hcombinedWarmSeed : 2 * lmGrowthDivisor n ≤ lm311CombinedStart n seed :=
    S.warm_large.trans (le_max_left _ _)
  have hcombinedWarmCarrier :
      2 * lmGrowthDivisor n ≤ lm311CombinedStart n carrierStart :=
    S.warm_large.trans (le_max_left _ _)
  have hcombinedCutSeed : (d : ℝ) / 128 ≤
      (lm311CombinedStart n seed : ℝ) :=
    hseedCut.trans (by exact_mod_cast (le_max_right (D ^ 4) seed))
  have hcombinedCutCarrier : (d : ℝ) / 128 ≤
      (lm311CombinedStart n carrierStart : ℝ) :=
    hcarrierCut.trans (by exact_mod_cast (le_max_right (D ^ 4) carrierStart))
  have hcombinedStartSeed : seed ≤ lm311CombinedStart n seed := le_max_right _ _
  have hcombinedStartCarrier : carrierStart ≤
      lm311CombinedStart n carrierStart := le_max_right _ _
  -/
  have setup : LM311SetupPackage n d :=
    lm311SetupPackage_of_scaleBounds S hd hdn
  have hDpos : 0 < D := by simpa [D] using S.expansion_pos
  have hDone : 1 ≤ D := hDpos
  have hDDelta : D ≤ Delta := by
    dsimp [Delta]
    nlinarith
  have hellpos : 0 < ell := by simpa [ell] using setup.ell_pos
  have hmpos : 0 < m := by simpa [m] using setup.m_pos
  have hlocalpos : 0 < localRounds := by
    simpa [localRounds] using setup.local_pos
  have hseedSources := setup.seed_sources
  have hseedCut : (d : ℝ) / 128 ≤ (seed : ℝ) := by
    simpa [seed] using lm311AdaptiveSeed_cutoff d
  have hcarrierSeed : seed ≤ carrierStart := by
    dsimp [seed, carrierStart, lm311CarrierStart]
    exact le_max_right _ _
  have hcarrierCut : (d : ℝ) / 128 ≤ (carrierStart : ℝ) :=
    hseedCut.trans (by exact_mod_cast hcarrierSeed)
  have hcarrierStartN : carrierStart ≤ n := by
    simpa [carrierStart] using setup.carrier_start_n
  have hcarrierStart_highHub : carrierStart ≤
      lm311HighHubSeed n d Delta 2 0 (3 * m + 1) := by
    simpa [carrierStart, Delta, D, m] using setup.carrier_high_hub
  have hcarrierStartDelta (hdDelta : d - 1 ≤ Delta) : carrierStart ≤ Delta := by
    have h := setup.carrier_delta (by simpa [Delta, D] using hdDelta)
    simpa [carrierStart, Delta, D] using h
  have hcombinedWarmSeed : 2 * lmGrowthDivisor n ≤ lm311CombinedStart n seed :=
    S.warm_large.trans (le_max_left _ _)
  have hcombinedWarmCarrier :
      2 * lmGrowthDivisor n ≤ lm311CombinedStart n carrierStart :=
    S.warm_large.trans (le_max_left _ _)
  /-
  have hrootRate : ∀ i < rounds, ∀ s : ℕ,
      lm311CombinedGrowth n d seed i ≤ s → s ≤ n / 2 →
      ((((lm311CombinedGain n d seed i + lm311HighFixedBudget 2 0 +
        (2 * (i + 2) + 1) + 2 ^ 2 * (i + 3) : ℕ) : ℝ)) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)) := by
    intro i hi s his hsn
    let cost := lm311HighFixedBudget 2 0 + (2 * (i + 2) + 1) +
      2 ^ 2 * (i + 3)
    have hlocalCost (hilocal : i < Parameters.lm311AdaptiveRounds n) :
        cost ≤ lm311AdaptiveGain d (lm311AdaptiveCurve d seed i) := by
      have hcost : lm311HighFixedBudget 2 0 + (2 * (i + 2) + 1) +
          2 ^ 2 * (i + 3) ≤ 6 * i + 40 := by
        dsimp [lm311HighFixedBudget]
        omega
      exact hcost.trans (lm311AdaptiveCost_le_gain (d := d) (i := i) hd)
    have hglobalCost : cost ≤ lm311GlobalCost n := by
      dsimp [cost, lm311HighFixedBudget, lm311GlobalCost, carrier,
        lm311CarrierCost, rounds, localRounds, m] at hi ⊢
      omega
    have hrate := lm311Combined_rate_of_scaleBounds S hd hseedCut hcombinedCutSeed
      (by simpa [rounds, localRounds, m] using hi) hlocalCost hglobalCost his hsn
    simpa only [cost, Nat.add_assoc] using hrate
  have hhubRate : ∀ i < rounds, ∀ s : ℕ,
      lm311CombinedGrowth n d carrierStart i ≤ s → s ≤ n / 2 →
      ((((lm311CombinedGain n d carrierStart i +
        lm311HighCarrierBudget n 2 0 (3 * m + 1) : ℕ) : ℝ)) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)) := by
    intro i hi s his hsn
    let cost := lm311HighCarrierBudget n 2 0 (3 * m + 1)
    have hlocalCost (_ : i < Parameters.lm311AdaptiveRounds n) :
        cost ≤ lm311AdaptiveGain d (lm311AdaptiveCurve d carrierStart i) := by
      have hbudget : cost ≤ carrier := by
        simpa [cost] using hcarrierBudget
      exact hbudget.trans
        (lm311CarrierCost_le_adaptiveGain_curve hn hd1 hcarrierStartN)
    have hglobalCost : cost ≤ lm311GlobalCost n := by
      have hbudget : cost ≤ carrier := by
        simpa [cost] using hcarrierBudget
      have hcarrierGlobal : carrier ≤ lm311GlobalCost n := by
        dsimp [carrier, lm311GlobalCost]
        omega
      exact hbudget.trans hcarrierGlobal
    have hrate := lm311Combined_rate_of_scaleBounds S hd hcarrierCut
      hcombinedCutCarrier (by simpa [rounds, localRounds, m] using hi)
      hlocalCost hglobalCost his hsn
    simpa only [cost] using hrate
  have hreservoirRate : ∀ i < localRounds, ∀ s : ℕ,
      lm311AdaptiveCurve d seed i ≤ s → s ≤ n / 2 →
      ((((lm311AdaptiveGain d (lm311AdaptiveCurve d seed i) + 2 * 2 ^ 2 +
        0 + 2 + (2 * (i + 2) + 1) : ℕ) : ℝ)) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)) := by
    intro i hi s his hsn
    have hcost : 2 * 2 ^ 2 + 0 + 2 + (2 * (i + 2) + 1) ≤ 6 * i + 40 := by omega
    have hcostGain : 2 * 2 ^ 2 + 0 + 2 + (2 * (i + 2) + 1) ≤
        lm311AdaptiveGain d (lm311AdaptiveCurve d seed i) :=
      hcost.trans (lm311AdaptiveCost_le_gain (d := d) (i := i) hd)
    have hrate := lm311AdaptiveGain_add_cost_le_expansion hd1
      (hseedCut.trans (by exact_mod_cast lm311AdaptiveCurve_start_le d seed i))
      his hcostGain
    simpa only [Nat.add_assoc] using hrate
  have hlowRootRate : ∀ i < rounds, ∀ s : ℕ,
      lm311CombinedGrowth n d seed i ≤ s → s ≤ n / 2 →
      ((((lm311CombinedGain n d seed i + 4 * 2 ^ 2 + 2 * 0 + 2 * 2 +
        (2 * (i + 2) + 1) + 2 ^ 2 * (i + 3) +
        (if i < ell then 0 else 2 ^ 2 * Delta) : ℕ) : ℝ)) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)) := by
    intro i hi s his hsn
    let cost := 4 * 2 ^ 2 + 2 * 0 + 2 * 2 + (2 * (i + 2) + 1) +
      2 ^ 2 * (i + 3) + (if i < ell then 0 else 2 ^ 2 * Delta)
    have hlocalCost (hilocal : i < Parameters.lm311AdaptiveRounds n) :
        cost ≤ lm311AdaptiveGain d (lm311AdaptiveCurve d seed i) := by
      have hiell : i < ell := by
        have hlocal : localRounds + 1 ≤ ell := by
          simpa [localRounds, ell] using S.local_radius
        have : i < localRounds := by simpa [localRounds] using hilocal
        omega
      have hcost : 4 * 2 ^ 2 + 2 * 0 + 2 * 2 + (2 * (i + 2) + 1) +
          2 ^ 2 * (i + 3) + 0 ≤ 6 * i + 40 := by omega
      rw [show cost = 4 * 2 ^ 2 + 2 * 0 + 2 * 2 + (2 * (i + 2) + 1) +
        2 ^ 2 * (i + 3) + 0 by simp [cost, hiell]]
      exact hcost.trans (lm311AdaptiveCost_le_gain (d := d) (i := i) hd)
    have hglobalCost : cost ≤ lm311GlobalCost n := by
      change 4 * 2 ^ 2 + 2 * 0 + 2 * 2 + (2 * (i + 2) + 1) +
          2 ^ 2 * (i + 3) + (if i < ell then 0 else 2 ^ 2 * Delta) ≤
        6 * rounds + carrier + 4 * Delta + 40
      have hi6 : 6 * i ≤ 6 * rounds := Nat.mul_le_mul_left 6 hi.le
      by_cases hiell : i < ell
      · rw [if_pos hiell]
        norm_num
        omega
      · rw [if_neg hiell]
        norm_num
        omega
    have hrate := lm311Combined_rate_of_scaleBounds S hd hseedCut hcombinedCutSeed
      (by simpa [rounds, localRounds, m] using hi) hlocalCost hglobalCost his hsn
    simpa only [cost, Nat.add_assoc] using hrate
  have hlowReservoirRate (hdDelta : d - 1 ≤ Delta) :
      ∀ i < rounds, ∀ s : ℕ,
      lm311CombinedGrowth n d carrierStart i ≤ s → s ≤ n / 2 →
      ((((lm311CombinedGain n d carrierStart i + 2 * 0 + 2 * 2 ^ 2 + 2 * 2 +
        lm311GirthBudget n + 2 ^ 2 * (3 * m + 1) +
        (if i < ell then 0 else 2 ^ 2 * Delta) : ℕ) : ℝ)) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)) := by
    intro i hi s his hsn
    let cost := 2 * 0 + 2 * 2 ^ 2 + 2 * 2 + lm311GirthBudget n +
      2 ^ 2 * (3 * m + 1) + (if i < ell then 0 else 2 ^ 2 * Delta)
    have hlocalCost (hilocal : i < Parameters.lm311AdaptiveRounds n) :
        cost ≤ lm311AdaptiveGain d (lm311AdaptiveCurve d carrierStart i) := by
      have hiell : i < ell := by
        have hlocal : localRounds + 1 ≤ ell := by
          simpa [localRounds, ell] using S.local_radius
        have : i < localRounds := by simpa [localRounds] using hilocal
        omega
      have hcost : 2 * 0 + 2 * 2 ^ 2 + 2 * 2 + lm311GirthBudget n +
          2 ^ 2 * (3 * m + 1) + 0 ≤ carrier := by
        dsimp [carrier, lm311CarrierCost]
        omega
      rw [show cost = 2 * 0 + 2 * 2 ^ 2 + 2 * 2 + lm311GirthBudget n +
        2 ^ 2 * (3 * m + 1) + 0 by simp [cost, hiell]]
      exact hcost.trans
        (lm311CarrierCost_le_adaptiveGain_curve hn hd1 hcarrierStartN)
    have hglobalCost : cost ≤ lm311GlobalCost n := by
      change 2 * 0 + 2 * 2 ^ 2 + 2 * 2 + lm311GirthBudget n +
          2 ^ 2 * (3 * m + 1) + (if i < ell then 0 else 2 ^ 2 * Delta) ≤
        6 * rounds + carrier + 4 * Delta + 40
      by_cases hiell : i < ell
      · rw [if_pos hiell]
        dsimp [carrier, lm311CarrierCost]
        norm_num
        omega
      · rw [if_neg hiell]
        dsimp [carrier, lm311CarrierCost]
        norm_num
        omega
    have hrate := lm311Combined_rate_of_scaleBounds S hd hcarrierCut
      hcombinedCutCarrier (by simpa [rounds, localRounds, m] using hi)
      hlocalCost hglobalCost his hsn
    simpa only [cost, Nat.add_assoc] using hrate
  -/
  have rates : LM311RatePackage n d := by
    apply lm311RatePackage_of_scaleBounds S hd
    simpa [carrierStart] using hcarrierStartN
  have hrootRate := rates.highRoot
  have hhubRate := rates.highHub
  have hreservoirRate := rates.reservoir
  have hlowRootRate := rates.lowRoot
  have hlowReservoirRate := rates.lowReservoir
  refine ⟨?_⟩
  refine
    { k_pos := by omega
      four_le_d := hd4
      D_pos := S.expansion_pos
      ell₀_pos := by simpa [ell] using hellpos
      m_pos := by simpa [m] using hmpos
      Delta_eq := rfl
      highRounds := rounds
      highRootGrowth := lm311CombinedGrowth n d seed
      highRootGain := lm311CombinedGain n d seed
      highHubGrowth := lm311CombinedGrowth n d carrierStart
      highHubGain := lm311CombinedGain n d carrierStart
      high_root_start := by
        rw [lm311CombinedGrowth_zero hlocalpos]
        exact hseedSources.1
      high_hub_start := by
        rw [lm311CombinedGrowth_zero hlocalpos]
        simpa [Delta, m] using hcarrierStart_highHub
      high_root_next := by
        intro i hi
        apply lm311Combined_next hd S.expansion_pos
        rfl
      high_hub_next := fun i _ ↦ lm311Combined_next hd S.expansion_pos hcarrierSeed
      high_root_lower := by
        intro i hi
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hseedCut
      high_hub_lower := by
        intro i hi
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hcarrierCut
      high_root_rate := by simpa [rounds, seed] using hrootRate
      high_hub_rate := by simpa [rounds, carrierStart, m] using hhubRate
      high_root_half := by
        simpa [rounds, seed] using lm311Combined_half hn hcombinedWarmSeed
      high_hub_half := by
        simpa [rounds, carrierStart] using lm311Combined_half hn hcombinedWarmCarrier
      high_connector := by
        have hlocal := S.local_radius
        have hfit := S.local_fit
        dsimp [rounds, localRounds, ell, m] at hlocal hfit ⊢
        omega
      high_star_budget := S.high_star
      packing := S.packing
      reservoirRounds := localRounds
      reservoirGrowth := lm311AdaptiveCurve d seed
      reservoirGain := fun i ↦ lm311AdaptiveGain d (lm311AdaptiveCurve d seed i)
      reservoir_radius := S.local_radius
      reservoir_start := by
        simpa [seed] using hseedSources.2.1
      reservoir_next := by intro i hi; exact (lm311AdaptiveCurve_succ d seed i).le
      reservoir_seed_lower := by
        intro i hi
        have hcurveNat := lm311AdaptiveCurve_start_le d seed i
        have hcurveReal : (seed : ℝ) ≤
            (lm311AdaptiveCurve d seed i : ℝ) := by exact_mod_cast hcurveNat
        have hcut := hseedCut.trans hcurveReal
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact hcut
      reservoir_rate := by simpa [localRounds, seed] using hreservoirRate
      reservoir_target := by
        have hwarm := lm311AdaptiveCurve_reaches_warmTarget
          (n := n) (d := d) hd S.expansion_pos
        have hsq : D ^ 2 ≤ D ^ 4 := by
          calc
            D ^ 2 = D ^ 2 * 1 := by ring
            _ ≤ D ^ 2 * D ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
            _ = D ^ 4 := by ring
        simpa [Delta, localRounds, seed, D] using hsq.trans hwarm
      reservoir_half := S.reservoir_half
      connectRounds := rounds
      lowRootGrowth := lm311CombinedGrowth n d seed
      lowRootGain := lm311CombinedGain n d seed
      lowReservoirGrowth := if d - 1 ≤ Delta then
        lm311CombinedGrowth n d carrierStart else fun _ ↦ 0
      lowReservoirGain := if d - 1 ≤ Delta then
        lm311CombinedGain n d carrierStart else fun _ ↦ 0
      low_root_start := by
        rw [lm311CombinedGrowth_zero hlocalpos]
        exact hseedSources.2.2
      low_reservoir_start := by
        by_cases hcase : d - 1 ≤ Delta
        · simp only [hcase, if_pos, lm311CombinedGrowth_zero hlocalpos]
          exact hcarrierStartDelta hcase
        · simp [hcase]
      low_root_next := by
        intro i hi
        apply lm311Combined_next hd S.expansion_pos
        rfl
      low_reservoir_next := by
        intro hdDelta i hi
        have hdLocal : d - 1 ≤ Delta := by
          simpa [Delta, D] using hdDelta
        rw [if_pos hdLocal, if_pos hdLocal]
        exact lm311Combined_next hd S.expansion_pos hcarrierSeed
      low_root_lower := by
        intro i hi
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hseedCut
      low_reservoir_lower := by
        intro hdDelta i hi
        rw [show ((1 / 64) * (d : ℝ)) / 2 = (d : ℝ) / 128 by ring]
        exact lm311Combined_lower hcarrierCut
      low_root_rate := by simpa [rounds, seed, ell, Delta] using hlowRootRate
      low_reservoir_rate := by
        intro hdDelta
        by_cases hdcase : d ≤ Parameters.lmExpansionOrder n ^ 2 + 1
        · have hdDelta' : d - 1 ≤ Delta := by
            dsimp [Delta, D]
            omega
          simpa [hdcase, rounds, carrierStart, ell, Delta, D, m] using
            hlowReservoirRate hdDelta'
        · have : d ≤ Parameters.lmExpansionOrder n ^ 2 + 1 := by omega
          exact (hdcase this).elim
      low_root_half := by
        simpa [rounds, seed] using lm311Combined_half hn hcombinedWarmSeed
      low_reservoir_half := by
        intro hdDelta
        simpa [rounds, carrierStart] using lm311Combined_half hn hcombinedWarmCarrier
      low_connector := by
        have hlocal := S.local_radius
        have hfit := S.local_fit
        dsimp [rounds, localRounds, ell, m] at hlocal hfit ⊢
        omega
      attach_radius := by
        have hfit : 3 * ell + 2 ≤ m := by
          simpa [ell, m] using S.local_fit
        omega
      low_star_budget := S.low_star }
  -/

/-- Final source-facing numerical package: one absolute degree threshold
works simultaneously for every `d ≤ n`, and the produced expansion radius
is bounded by the radius used in Theorem 2.7. -/
theorem eventually_exists_lm311Numerics :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ n : ℕ, d ≤ n →
      ∃ num : LM311Numerics (1 / 1024) ((1 / 64) * (d : ℝ)) n 2 d
          (Parameters.lmExpansionOrder n) (Parameters.lmExpansionOrder n ^ 2)
          (Parameters.lm311LocalRadius n) (lmGrowthRounds n) 0,
        5 * lmGrowthRounds n ≤ Parameters.lmRadius (1 / 1024) n := by
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp eventually_lm311ScaleBounds
  refine ⟨max lm311DegreeThreshold n₀, ?_⟩
  intro d hd n hdn
  have hdegree : lm311DegreeThreshold ≤ d :=
    (le_max_left _ _).trans hd
  have hn₀n : n₀ ≤ n := (le_max_right _ _).trans (hd.trans hdn)
  let S := hn₀ n hn₀n
  obtain ⟨num⟩ := lm311NumericsOfScaleBounds S hdegree hdn
  exact ⟨num, five_mul_lmGrowthRounds_le_lmRadius S.card_large⟩

/-! ## Direct-or-bootstrap seeds -/

/-- The source uses a set itself when it is above the expander cutoff and a
radius-one minimum-degree bootstrap otherwise.  In the bootstrap branch we
remove the paid workspace from the degree lower bound. -/
def lmSeedStart (d base workspace : ℕ) : ℕ :=
  if d ≤ 128 * base then base else d - workspace

theorem lmSeedStart_base_le {d base workspace : ℕ}
    (hworkspace : workspace ≤ base) :
    base ≤ lmSeedStart d base workspace := by
  rw [lmSeedStart]
  split_ifs with h
  · exact le_rfl
  · omega

theorem lmSeedStart_cutoff {d base workspace : ℕ}
    (hworkspace : workspace ≤ base) :
    (d : ℝ) / 128 ≤ (lmSeedStart d base workspace : ℝ) := by
  rw [lmSeedStart]
  split_ifs with h
  · have hreal : (d : ℝ) ≤ 128 * (base : ℝ) := by exact_mod_cast h
    linarith
  · have hnat : d ≤ 128 * (d - workspace) := by omega
    have hreal : (d : ℝ) ≤ 128 * ((d - workspace : ℕ) : ℝ) := by
      exact_mod_cast hnat
    linarith

theorem lmSeedStart_direct_or_bootstrap {d base workspace : ℕ}
    (hworkspace : workspace ≤ base) :
    lmSeedStart d base workspace ≤ base ∨
      lmSeedStart d base workspace + workspace ≤ d := by
  rw [lmSeedStart]
  split_ifs with h
  · exact Or.inl le_rfl
  · right
    have hwd : workspace ≤ d := hworkspace.trans (by omega)
    omega

/-! ## Eventual source parameters -/

/-- The schedule-free numerical package consumed by the source-level
adjuster and exact-path assemblers.  Its workspace field absorbs every paid
set of order at most `500 * radius^2`; the endpoint expansions themselves
have order `lmExpansionOrder n` and are not part of that workspace. -/
structure LMConcreteGrowthBounds (n d : ℕ) : Prop where
  card_large : 32 ≤ n
  degree_pos : 1 ≤ d
  endpoint_large :
    2 * lmGrowthDivisor n ≤ 2 * Parameters.lmExpansionOrder n
  workspace_absorbed :
    500 * Parameters.lmRadius (1 / 1024) n ^ 2 ≤
      lmGrowthGain n (2 * Parameters.lmExpansionOrder n)
  rounds_le_radius :
    lmGrowthRounds n ≤ Parameters.lmRadius (1 / 1024) n
  connector_radius :
    2 * (lmGrowthRounds n + 1) ≤ Parameters.lmRadius (1 / 1024) n

/-- All concrete growth inequalities hold uniformly for every positive
minimum-degree scale.  Whether a particular seed grows directly or after the
radius-one degree bootstrap is decided by `lmSeedStart`; there is no
comparison between `d` and the polylogarithmic endpoint order. -/
theorem eventually_lmConcreteGrowthBounds :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ d : ℕ, 1 ≤ d → LMConcreteGrowthBounds n d := by
  have hlogtop : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog := hlogtop.eventually (Filter.eventually_ge_atTop (9217 : ℝ))
  have hcore := Parameters.eventually_core_le_expansionOrder_div_logCubeCeil
    (show (0 : ℝ) < 1 / 1024 by norm_num)
  filter_upwards [Filter.eventually_ge_atTop 32, hlog, hcore] with n hn hnlog hncore
  intro d hd
  let L := Real.log (n : ℝ)
  let M := Parameters.lmLogCubeCeil n
  let D := Parameters.lmExpansionOrder n
  have hL : (9217 : ℝ) ≤ L := by simpa [L] using hnlog
  have hLone : (1 : ℝ) ≤ L := by linarith
  have hMlower : L ^ 3 ≤ (M : ℝ) := by
    simpa only [L, M, Parameters.lmLogCubeCeil] using
      (Nat.le_ceil (Real.log (n : ℝ) ^ 3))
  have hMupper : (M : ℝ) ≤ 2 * L ^ 3 := by
    simpa [L, M] using
      (Parameters.lmLogCubeCeil_bounds (n := n) (one_le_pow₀ hLone)).2
  have hMpos : 0 < M := by
    have hreal : (0 : ℝ) < (M : ℝ) :=
      (pow_pos (zero_lt_one.trans_le hLone) 3).trans_le hMlower
    exact_mod_cast hreal
  have hdenM : lmGrowthDenominator n ≤ M := by
    apply Nat.ceil_le.mpr
    calc
      9216 * Real.log (n : ℝ) ^ 2 ≤ L ^ 3 := by
        change 9216 * L ^ 2 ≤ L ^ 3
        have := mul_le_mul_of_nonneg_right hL (sq_nonneg L)
        nlinarith
      _ ≤ (M : ℝ) := hMlower
  have hdenpos : 0 < lmGrowthDenominator n :=
    lmGrowthDenominator_pos (hn.trans' (by omega))
  have hDlower : L ^ 10 ≤ (D : ℝ) := by
    simpa [L, D] using Parameters.lmExpansionOrder_lower n
  have htwoM_D : 2 * M ≤ D := by
    have hreal : ((2 * M : ℕ) : ℝ) ≤ (D : ℝ) := by
      push_cast
      calc
        2 * (M : ℝ) ≤ 4 * L ^ 3 := by nlinarith
        _ ≤ L ^ 10 := by
          have hL7 : (4 : ℝ) ≤ L ^ 7 := by
            have hbase : (4 : ℝ) ≤ L := by linarith
            have hpow : 1 ≤ L ^ 6 := one_le_pow₀ hLone
            exact hbase.trans (by nlinarith)
          calc
            4 * L ^ 3 ≤ L ^ 7 * L ^ 3 :=
              mul_le_mul_of_nonneg_right hL7 (pow_nonneg (by linarith) 3)
            _ = L ^ 10 := by ring
        _ ≤ (D : ℝ) := hDlower
    exact_mod_cast hreal
  have hendpoint : 2 * lmGrowthDivisor n ≤ 2 * D := by
    dsimp [lmGrowthDivisor]
    omega
  have hgainEq : lmGrowthGain n (2 * D) = D / lmGrowthDenominator n := by
    simpa [lmGrowthGain, lmGrowthDivisor, Nat.mul_comm] using
      (Nat.mul_div_mul_left D (lmGrowthDenominator n) (by omega : 0 < 2))
  have hden2M : lmGrowthDenominator n ≤ 2 * M := by omega
  have hdiv : D / (2 * M) ≤ D / lmGrowthDenominator n :=
    Nat.div_le_div_left hden2M hdenpos
  have hworkspace :
      500 * Parameters.lmRadius (1 / 1024) n ^ 2 ≤
        lmGrowthGain n (2 * D) := by
    rw [hgainEq]
    have hcore' : 500 * Parameters.lmRadius (1 / 1024) n ^ 2 ≤ D / (2 * M) := by
      simpa only [D, M] using hncore
    exact hcore'.trans hdiv
  exact
    { card_large := hn
      degree_pos := hd
      endpoint_large := by simpa [D] using hendpoint
      workspace_absorbed := by simpa [D] using hworkspace
      rounds_le_radius := lmGrowthRounds_le_lmRadius hn
      connector_radius := by
        have hroundpos : 1 ≤ lmGrowthRounds n := by
          have hdivpos := lmGrowthDivisor_pos (hn.trans' (by omega))
          dsimp [lmGrowthRounds]
          exact Nat.mul_pos (Nat.mul_pos (by omega) hdivpos) (by omega)
        have hle : 2 * (lmGrowthRounds n + 1) ≤ 7 * lmGrowthRounds n := by omega
        exact hle.trans (seven_mul_lmGrowthRounds_le_lmRadius hn) }

/-! ## Final Lemma 4.7 scale certificate -/

/-- Three copies of the simple-adjuster radius fit inside the chained radius
once the underlying logarithmic scale is at least three.  The extra unit
lost by each ceiling is absorbed by the unused fourth copy. -/
theorem three_mul_lmSimpleRadius_le_lmRadius
    {ε₁ : ℝ} {n : ℕ} (hε₁ : 0 < ε₁)
    (hlarge : 3 ≤ (400 / ε₁) * Real.log (n : ℝ) ^ 3) :
    3 * Parameters.lmSimpleRadius ε₁ n ≤ Parameters.lmRadius ε₁ n := by
  let x := (400 / ε₁) * Real.log (n : ℝ) ^ 3
  have hs : (Parameters.lmSimpleRadius ε₁ n : ℝ) < x + 1 := by
    simpa [x] using Parameters.lmSimpleRadius_lt_add_one (n := n) hε₁
  have hr : 4 * x ≤ (Parameters.lmRadius ε₁ n : ℝ) := by
    have hscale :
        (1600 / ε₁) * Real.log (n : ℝ) ^ 3 = 4 * x := by
      dsimp [x]
      ring
    rw [← hscale]
    exact Parameters.lmRadius_lower ε₁ n
  have hthree : (3 : ℝ) ≤ x := by simpa [x] using hlarge
  have hcast : ((3 * Parameters.lmSimpleRadius ε₁ n : ℕ) : ℝ) ≤
      (Parameters.lmRadius ε₁ n : ℝ) := by
    push_cast
    exact le_of_lt <| calc
      3 * (Parameters.lmSimpleRadius ε₁ n : ℝ)
          < 3 * (x + 1) := mul_lt_mul_of_pos_left hs (by norm_num)
      _ ≤ 4 * x := by linarith
      _ ≤ (Parameters.lmRadius ε₁ n : ℝ) := hr
  exact_mod_cast hcast

/-- Inflated end order used in the corrected proof of Lemma 4.7. -/
noncomputable def lm47InflatedOrder (n : ℕ) : ℕ :=
  Parameters.lmExpansionOrder n * Parameters.lmRadius (1 / 1024) n

/-- Supply budget for the corrected Lemma 4.7 induction. -/
noncomputable def lm47SimpleBudget (n : ℕ) : ℕ :=
  6 * lm47InflatedOrder n

/-- Paid connector workspace.  The `2D` term is the union of the two
preconstructed endpoint expansions; only the remaining `500m²` is used by
adjuster cores and short routes. -/
noncomputable def lm47Workspace (n : ℕ) : ℕ :=
  2 * Parameters.lmExpansionOrder n +
    500 * Parameters.lmRadius (1 / 1024) n ^ 2

/-- The arithmetic facts left by the corrected `r = 22m` application of
Lemma 4.7.  Joining is performed at end order `M = Dm`, so the two protected
`D`-expansions can be charged in the ordinary connector deletion. -/
structure LM47ScaleBounds (n : ℕ) : Prop where
  endpoint_pos : 0 < Parameters.lmExpansionOrder n
  shrink_le : Parameters.lmExpansionOrder n ≤ lm47InflatedOrder n
  simple_radius_le :
    2 * Parameters.lmSimpleRadius (1 / 1024) n ≤
      Parameters.lmRadius (1 / 1024) n
  inflated_endpoint_large :
    2 * lmGrowthDivisor n ≤ 2 * lm47InflatedOrder n
  inflated_workspace_absorbed :
    lm47Workspace n ≤ lmGrowthGain n (2 * lm47InflatedOrder n)
  supply_capacity :
    2 * Parameters.lmExpansionOrder n + 2 * lm47InflatedOrder n +
        220 * Parameters.lmRadius (1 / 1024) n ^ 2 ≤
      lm47SimpleBudget n
  workspace_capacity :
    2 * Parameters.lmExpansionOrder n +
        220 * Parameters.lmRadius (1 / 1024) n ^ 2 +
        10 * (2 * Parameters.lmSimpleRadius (1 / 1024) n) ≤
      lm47Workspace n
  join_capacity :
    10 * (2 * Parameters.lmSimpleRadius (1 / 1024) n) +
        (Parameters.lmRadius (1 / 1024) n +
          2 * (lmGrowthRounds n + 1) +
          2 * Parameters.lmSimpleRadius (1 / 1024) n) + 1 ≤
      10 * Parameters.lmRadius (1 / 1024) n

/-- Thus the final schedule-free Lemma 4.7 call has no residual asymptotic
arithmetic obligations.  This statement is independent of the degree scale.
The direct-or-bootstrap connector handles every positive minimum degree. -/
theorem eventually_lm47ScaleBounds :
    ∀ᶠ n : ℕ in Filter.atTop, LM47ScaleBounds n := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ 3)
      Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (show 3 ≠ 0 by norm_num)).comp hlog
  have hscale : Filter.Tendsto
      (fun n : ℕ ↦ (400 / (1 / 1024 : ℝ)) * Real.log (n : ℝ) ^ 3)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) hpow
  have hscaleLarge := hscale.eventually (Filter.eventually_ge_atTop (3 : ℝ))
  filter_upwards [eventually_lmConcreteGrowthBounds, hscaleLarge] with n hb hlarge
  let s := Parameters.lmSimpleRadius (1 / 1024) n
  let m := Parameters.lmRadius (1 / 1024) n
  let D := Parameters.lmExpansionOrder n
  let R := lmGrowthRounds n
  have B := hb 1 (by omega)
  have hthree : 3 * s ≤ m := by
    simpa [s, m] using
      (three_mul_lmSimpleRadius_le_lmRadius
        (n := n) (by norm_num : (0 : ℝ) < 1 / 1024) hlarge)
  have hslarge : 3 ≤ s := by
    have hsreal : (3 : ℝ) ≤ (s : ℝ) := by
      exact hlarge.trans (by
        simpa [s] using Parameters.lmSimpleRadius_lower (1 / 1024 : ℝ) n)
    exact_mod_cast hsreal
  have hmlarge : 9 ≤ m := by omega
  have hmone : 1 ≤ m := by omega
  have hmm : m ≤ m ^ 2 := by
    calc
      m = m * 1 := by simp
      _ ≤ m * m := Nat.mul_le_mul_left m hmone
      _ = m ^ 2 := by ring
  have hsimple : 2 * s ≤ m := by omega
  have hrounds : 7 * R ≤ m := by
    simpa [R, m] using seven_mul_lmGrowthRounds_le_lmRadius B.card_large
  let M := D * m
  have hgainle : lmGrowthGain n (2 * D) ≤ 2 * D := Nat.div_le_self _ _
  have hworkspaceD : 500 * m ^ 2 ≤ 2 * D := by
    have hbase : 500 * m ^ 2 ≤ lmGrowthGain n (2 * D) := by
      simpa [m, D] using B.workspace_absorbed
    exact hbase.trans hgainle
  have hDpos : 0 < D := by
    have hdivpos := lmGrowthDivisor_pos (B.card_large.trans' (by omega))
    have hendpoint : 2 * lmGrowthDivisor n ≤ 2 * D := by
      simpa [D] using B.endpoint_large
    omega
  have hDM : D ≤ M := by
    dsimp [M]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left D hmone
  have hlargeM : 2 * lmGrowthDivisor n ≤ 2 * M := by
    exact B.endpoint_large.trans (Nat.mul_le_mul_left 2 hDM)
  have hdivR : 2 * lmGrowthDivisor n ≤ R := by
    dsimp [R, lmGrowthRounds]
    have hfactor : 1 ≤ Nat.log 2 n + 1 := by omega
    exact Nat.le_mul_of_pos_right _ hfactor
  have hdivm : 2 * lmGrowthDivisor n ≤ m := by
    exact hdivR.trans ((by omega : R ≤ 7 * R).trans hrounds)
  have hfourDGain : 4 * D ≤ lmGrowthGain n (2 * M) := by
    rw [lmGrowthGain]
    apply (Nat.le_div_iff_mul_le
      (lmGrowthDivisor_pos (B.card_large.trans' (by omega)))).2
    calc
      4 * D * lmGrowthDivisor n = 2 * D * (2 * lmGrowthDivisor n) := by ring
      _ ≤ 2 * D * m := Nat.mul_le_mul_left (2 * D) hdivm
      _ = 2 * M := by simp [M, mul_assoc]
  have hpaid : 2 * D + 500 * m ^ 2 ≤
      lmGrowthGain n (2 * M) := by
    have hfour : 2 * D + 500 * m ^ 2 ≤ 4 * D := by omega
    exact hfour.trans hfourDGain
  have hsupply : 2 * D + 2 * M + 220 * m ^ 2 ≤ 6 * M := by omega
  have hworkspace :
      2 * D + 220 * m ^ 2 + 10 * (2 * s) ≤ 2 * D + 500 * m ^ 2 := by
    omega
  have hthreeSimple : 3 * (2 * s) ≤ 2 * m := by omega
  have hjoin :
      10 * (2 * s) + (m + 2 * (R + 1) + 2 * s) + 1 ≤ 10 * m := by
    omega
  exact
    { endpoint_pos := by simpa [D] using hDpos
      shrink_le := by simpa [D, m, M, lm47InflatedOrder] using hDM
      simple_radius_le := by simpa [s, m] using hsimple
      inflated_endpoint_large := by
        simpa [D, m, M, lm47InflatedOrder] using hlargeM
      inflated_workspace_absorbed := by
        simpa [D, m, M, lm47InflatedOrder, lm47Workspace] using hpaid
      supply_capacity := by
        simpa [D, m, M, lm47InflatedOrder, lm47SimpleBudget] using hsupply
      workspace_capacity := by
        simpa [D, m, s, lm47Workspace] using hworkspace
      join_capacity := by simpa [s, m, R] using hjoin }

/-! ## Concrete instances of the two existing schedule interfaces -/

/-- Concrete `LMConnectorSchedule`.  The budget hypothesis is intentionally
stated only for the genuinely blocked part of the construction. -/
noncomputable def concreteLMConnectorSchedule
    (N d D workspace : ℕ) (hN : 32 ≤ N) (hd : 1 ≤ d)
    (hcutoff : (d : ℝ) / 128 ≤ (D : ℝ))
    (hlarge : 2 * lmGrowthDivisor N ≤ D)
    (hworkspace : workspace ≤ lmGrowthGain N D) :
    LMConnectorSchedule (1 / 1024) ((1 / 64) * (d : ℝ)) N D workspace where
  rounds := lmGrowthRounds N
  lower := lmGrowthCurve N D
  increment := fun i ↦ lmGrowthGain N (lmGrowthCurve N D i)
  lower_zero := by simp
  lower_mono := lmGrowthCurve_mono N D
  seed := by
    calc
      ((1 / 64 : ℝ) * (d : ℝ)) / 2 = (d : ℝ) / 128 := by ring
      _ ≤ (D : ℝ) := hcutoff
  step_target := by intro i _; simp
  rate := by
    intro i _ s his hsNhalf
    have hDs : D ≤ s := (lmGrowthCurve_start_le N D i).trans his
    have hcutoffS : (d : ℝ) / 128 ≤ (s : ℝ) :=
      hcutoff.trans (by exact_mod_cast hDs)
    have hgainD : lmGrowthGain N D ≤ lmGrowthGain N s :=
      lmGrowthGain_mono N hDs
    have hgainI : lmGrowthGain N (lmGrowthCurve N D i) ≤ lmGrowthGain N s :=
      lmGrowthGain_mono N his
    have hnat : workspace + lmGrowthGain N (lmGrowthCurve N D i) ≤
        2 * lmGrowthGain N s := by omega
    have hnatReal : ((workspace + lmGrowthGain N (lmGrowthCurve N D i) : ℕ) : ℝ) ≤
        ((2 * lmGrowthGain N s : ℕ) : ℝ) := by
      exact_mod_cast hnat
    exact hnatReal.trans <|
      two_lmGrowthGain_le_expansion hN hd hcutoffS
        (hsNhalf.trans (Nat.div_le_self N 2))
  reaches_half := lmGrowthCurve_reaches_half hN hlarge

/-- Graph-free multiplicative growth data for the two connectors in Lemma 4.2.

The hypotheses expose exactly the scalar estimates needed by the natural
`lmGrowthCurve`: the starting set lies above the expander cutoff, is large
enough for the doubling argument, and pays the fixed workspace out of its
first growth increment. -/
noncomputable def concreteLM42GrowthSchedule
    (N d start workspace : ℕ) (hN : 32 ≤ N) (hd : 1 ≤ d)
    (hcutoff : (d : ℝ) / 128 ≤ (start : ℝ))
    (hlarge : 2 * lmGrowthDivisor N ≤ start)
    (hworkspace : workspace ≤ lmGrowthGain N start) :
    LM42GrowthSchedule N start workspace (lmGrowthRounds N)
      (1 / 1024) ((1 / 64) * (d : ℝ)) where
  size := lmGrowthCurve N start
  initial := by simp
  lower := by
    intro i _
    have hstarti := lmGrowthCurve_start_le N start i
    have hstartReal : (start : ℝ) ≤ (lmGrowthCurve N start i : ℝ) := by
      exact_mod_cast hstarti
    calc
      ((1 / 64 : ℝ) * (d : ℝ)) / 2 = (d : ℝ) / 128 := by ring
      _ ≤ (start : ℝ) := hcutoff
      _ ≤ _ := hstartReal
  target := lmGrowthCurve_reaches_half hN hlarge
  step := by
    intro i _ s his hsNhalf
    have hstarts : start ≤ s := (lmGrowthCurve_start_le N start i).trans his
    have hcutoffS : (d : ℝ) / 128 ≤ (s : ℝ) :=
      hcutoff.trans (by exact_mod_cast hstarts)
    have hnext :
        lmGrowthCurve N start (i + 1) - s ≤ lmGrowthGain N s := by
      rw [lmGrowthCurve_succ]
      have hgain := lmGrowthGain_mono N his
      have hsub :
          lmGrowthCurve N start i + lmGrowthGain N (lmGrowthCurve N start i) - s ≤
            lmGrowthGain N (lmGrowthCurve N start i) := by
        omega
      exact hsub.trans hgain
    have hgainStart : lmGrowthGain N start ≤ lmGrowthGain N s :=
      lmGrowthGain_mono N hstarts
    have hnat : workspace + (lmGrowthCurve N start (i + 1) - s) ≤
        2 * lmGrowthGain N s := by
      calc
        workspace + (lmGrowthCurve N start (i + 1) - s) ≤
            lmGrowthGain N s + lmGrowthGain N s :=
          Nat.add_le_add (hworkspace.trans hgainStart) hnext
        _ = 2 * lmGrowthGain N s := by omega
    have hnatReal :
        ((workspace + (lmGrowthCurve N start (i + 1) - s) : ℕ) : ℝ) ≤
          ((2 * lmGrowthGain N s : ℕ) : ℝ) := by
      exact_mod_cast hnat
    exact hnatReal.trans <|
      two_lmGrowthGain_le_expansion hN hd hcutoffS
        (hsNhalf.trans (Nat.div_le_self N 2))

/-- Assemble the complete graph-free connector scale for Lemma 4.2 from the
two endpoint orders `m^2 D` and `m^3 D`.

The square and cube workspaces remain separate, matching the actual deleted
sets in the two connector calls.  Both use the canonical multiplicative
clock; the two path-radius hypotheses are kept separate so callers can
discharge them from whichever ambient radius estimates they have available. -/
noncomputable def concreteLM42ConnectorScale
    (N d D m cycleLength squareWorkspace cubeWorkspace : ℕ)
    (hN : 32 ≤ N) (hd : 1 ≤ d) (hm : 2 ≤ m) (hD : 0 < D)
    (hSquareWorkspaceLarge :
      cycleLength + 2 + (3 * m + 1) + 2 * D ≤ squareWorkspace)
    (hCubeWorkspaceLarge :
      cycleLength + 2 + 2 * D + 2 * (m ^ 2 * D) ≤ cubeWorkspace)
    (hSquareSeed : lm311AdaptiveSeed d ≤ m ^ 2 * D ∨
      lm311AdaptiveSeed d + squareWorkspace ≤ d - 1)
    (hCubeSeed : lm311AdaptiveSeed d ≤ m ^ 3 * D ∨
      lm311AdaptiveSeed d + cubeWorkspace ≤ d - 1)
    (hSquareLarge : 2 * lmGrowthDivisor N ≤ m ^ 2 * D)
    (hCubeLarge : 2 * lmGrowthDivisor N ≤ m ^ 3 * D)
    (hSquareWorkspace : squareWorkspace ≤ lmGrowthGain N (m ^ 2 * D))
    (hCubeWorkspace : cubeWorkspace ≤ lmGrowthGain N (m ^ 3 * D))
    (hSquareRadius : 2 * (lmGrowthRounds N + 1) ≤ m)
    (hCubeRadius : 2 * (lmGrowthRounds N + 1) ≤ m)
    (hCycleLength : cycleLength ≤ 2 * m) :
    LM42ConnectorScale N d D m cycleLength
      (1 / 1024) ((1 / 64) * (d : ℝ)) := by
  let squareStart := max (lm311AdaptiveSeed d) (m ^ 2 * D)
  let cubeStart := max (lm311AdaptiveSeed d) (m ^ 3 * D)
  have hSquareCutoff : (d : ℝ) / 128 ≤ (squareStart : ℝ) :=
    (lm311AdaptiveSeed_cutoff d).trans (by exact_mod_cast le_max_left _ _)
  have hCubeCutoff : (d : ℝ) / 128 ≤ (cubeStart : ℝ) :=
    (lm311AdaptiveSeed_cutoff d).trans (by exact_mod_cast le_max_left _ _)
  have hSquareLarge' : 2 * lmGrowthDivisor N ≤ squareStart :=
    hSquareLarge.trans (le_max_right _ _)
  have hCubeLarge' : 2 * lmGrowthDivisor N ≤ cubeStart :=
    hCubeLarge.trans (le_max_right _ _)
  have hSquareWorkspace' : squareWorkspace ≤ lmGrowthGain N squareStart :=
    hSquareWorkspace.trans (lmGrowthGain_mono N (le_max_right _ _))
  have hCubeWorkspace' : cubeWorkspace ≤ lmGrowthGain N cubeStart :=
    hCubeWorkspace.trans (lmGrowthGain_mono N (le_max_right _ _))
  refine {
  squareWorkspace := squareWorkspace
  cubeWorkspace := cubeWorkspace
  squareStart := squareStart
  cubeStart := cubeStart
  squareRadius := lmGrowthRounds N
  cubeRadius := lmGrowthRounds N
  two_le_m := hm
  D_pos := hD
  connector_workspace_large := hCubeWorkspaceLarge
  connector_workspace_path := hSquareWorkspaceLarge
  squareSeed := by
    rcases hSquareSeed with hsource | hdegree
    · left
      simpa [squareStart, max_eq_right hsource]
    · by_cases hsource : lm311AdaptiveSeed d ≤ m ^ 2 * D
      · left
        simpa [squareStart, max_eq_right hsource]
      · right
        have hreverse : m ^ 2 * D ≤ lm311AdaptiveSeed d :=
          Nat.le_of_lt (Nat.lt_of_not_ge hsource)
        simpa [squareStart, max_eq_left hreverse] using hdegree
  cubeSeed := by
    rcases hCubeSeed with hsource | hdegree
    · left
      simpa [cubeStart, max_eq_right hsource]
    · by_cases hsource : lm311AdaptiveSeed d ≤ m ^ 3 * D
      · left
        simpa [cubeStart, max_eq_right hsource]
      · right
        have hreverse : m ^ 3 * D ≤ lm311AdaptiveSeed d :=
          Nat.le_of_lt (Nat.lt_of_not_ge hsource)
        simpa [cubeStart, max_eq_left hreverse] using hdegree
  squareGrowth := concreteLM42GrowthSchedule N d squareStart squareWorkspace
    hN hd hSquareCutoff hSquareLarge' hSquareWorkspace'
  cubeGrowth := concreteLM42GrowthSchedule N d cubeStart cubeWorkspace
    hN hd hCubeCutoff hCubeLarge' hCubeWorkspace'
  square_path_radius := hSquareRadius
  cube_path_radius := hCubeRadius
  cycle_length := hCycleLength }

/-- Concrete `BallGrowthSchedule` with the same multiplicative curve. -/
noncomputable def concreteBallGrowthSchedule
    [Fintype V] (G : SimpleGraph V) (d D workspace : ℕ)
    (hN : 32 ≤ Fintype.card V) (hd : 1 ≤ d)
    (hcutoff : (d : ℝ) / 128 ≤ (D : ℝ))
    (hlarge : 2 * lmGrowthDivisor (Fintype.card V) ≤ D)
    (hworkspace : workspace ≤ lmGrowthGain (Fintype.card V) D) :
    BallGrowthSchedule G (1 / 1024) ((1 / 64) * (d : ℝ)) D workspace
      (lmGrowthRounds (Fintype.card V)) where
  size := lmGrowthCurve (Fintype.card V) D
  initial := by simp
  lower := by
    intro i _
    have hDi := lmGrowthCurve_start_le (Fintype.card V) D i
    have hDreal : (D : ℝ) ≤
        (lmGrowthCurve (Fintype.card V) D i : ℝ) := by
      exact_mod_cast hDi
    calc
      ((1 / 64 : ℝ) * (d : ℝ)) / 2 = (d : ℝ) / 128 := by ring
      _ ≤ (D : ℝ) := hcutoff
      _ ≤ _ := hDreal
  target := lmGrowthCurve_reaches_half hN hlarge
  step := by
    intro i _ s his hsNhalf
    let N := Fintype.card V
    change lmGrowthCurve N D i ≤ s at his
    have hDs : D ≤ s := (lmGrowthCurve_start_le N D i).trans his
    have hcutoffS : (d : ℝ) / 128 ≤ (s : ℝ) :=
      hcutoff.trans (by exact_mod_cast hDs)
    have hnext :
        lmGrowthCurve N D (i + 1) - s ≤ lmGrowthGain N s := by
      rw [lmGrowthCurve_succ]
      have hgain := lmGrowthGain_mono N his
      have hsub : lmGrowthCurve N D i + lmGrowthGain N (lmGrowthCurve N D i) - s ≤
          lmGrowthGain N (lmGrowthCurve N D i) := by omega
      exact hsub.trans hgain
    have hgainD : lmGrowthGain N D ≤ lmGrowthGain N s :=
      lmGrowthGain_mono N hDs
    have hnat : workspace + (lmGrowthCurve N D (i + 1) - s) ≤
        2 * lmGrowthGain N s := by
      calc
        workspace + (lmGrowthCurve N D (i + 1) - s) ≤
            lmGrowthGain N s + lmGrowthGain N s :=
          Nat.add_le_add (hworkspace.trans hgainD) hnext
        _ = 2 * lmGrowthGain N s := by omega
    have hnatReal : ((workspace + (lmGrowthCurve N D (i + 1) - s) : ℕ) : ℝ) ≤
        ((2 * lmGrowthGain N s : ℕ) : ℝ) := by
      exact_mod_cast hnat
    exact hnatReal.trans <|
      two_lmGrowthGain_le_expansion hN hd hcutoffS
        (hsNhalf.trans (Nat.div_le_self N 2))

/-- The same concrete curve stopped at an arbitrary certified target
radius.  This is used at the `n/8` bulk scale, where three doubling blocks
rather than `log n` blocks suffice. -/
noncomputable def concreteBallGrowthScheduleOfTarget
    [Fintype V] (G : SimpleGraph V) (d D workspace radius : ℕ)
    (hN : 32 ≤ Fintype.card V) (hd : 1 ≤ d)
    (hcutoff : (d : ℝ) / 128 ≤ (D : ℝ))
    (hworkspace : workspace ≤ lmGrowthGain (Fintype.card V) D)
    (htarget : Fintype.card V / 2 + 1 ≤
      lmGrowthCurve (Fintype.card V) D radius) :
    BallGrowthSchedule G (1 / 1024) ((1 / 64) * (d : ℝ)) D workspace radius where
  size := lmGrowthCurve (Fintype.card V) D
  initial := by simp
  lower := by
    intro i _
    have hDi := lmGrowthCurve_start_le (Fintype.card V) D i
    have hDreal : (D : ℝ) ≤
        (lmGrowthCurve (Fintype.card V) D i : ℝ) := by
      exact_mod_cast hDi
    calc
      ((1 / 64 : ℝ) * (d : ℝ)) / 2 = (d : ℝ) / 128 := by ring
      _ ≤ (D : ℝ) := hcutoff
      _ ≤ _ := hDreal
  target := htarget
  step := by
    intro i _ s his hsNhalf
    let N := Fintype.card V
    change lmGrowthCurve N D i ≤ s at his
    have hDs : D ≤ s := (lmGrowthCurve_start_le N D i).trans his
    have hcutoffS : (d : ℝ) / 128 ≤ (s : ℝ) :=
      hcutoff.trans (by exact_mod_cast hDs)
    have hnext :
        lmGrowthCurve N D (i + 1) - s ≤ lmGrowthGain N s := by
      rw [lmGrowthCurve_succ]
      have hgain := lmGrowthGain_mono N his
      have hsub : lmGrowthCurve N D i + lmGrowthGain N (lmGrowthCurve N D i) - s ≤
          lmGrowthGain N (lmGrowthCurve N D i) := by omega
      exact hsub.trans hgain
    have hgainD : lmGrowthGain N D ≤ lmGrowthGain N s :=
      lmGrowthGain_mono N hDs
    have hnat : workspace + (lmGrowthCurve N D (i + 1) - s) ≤
        2 * lmGrowthGain N s := by
      calc
        workspace + (lmGrowthCurve N D (i + 1) - s) ≤
            lmGrowthGain N s + lmGrowthGain N s :=
          Nat.add_le_add (hworkspace.trans hgainD) hnext
        _ = 2 * lmGrowthGain N s := by omega
    have hnatReal : ((workspace + (lmGrowthCurve N D (i + 1) - s) : ℕ) : ℝ) ≤
        ((2 * lmGrowthGain N s : ℕ) : ℝ) := by
      exact_mod_cast hnat
    exact hnatReal.trans <|
      two_lmGrowthGain_le_expansion hN hd hcutoffS
        (hsNhalf.trans (Nat.div_le_self N 2))

/-! ## The concrete scales for Corollary 3.15 -/

/-- The sharp Claim 4.6 far radius fits inside one quarter of the simple
adjuster radius.  The explicit coefficients are
`4 * 3 * 9217 * (5/3) = 184340 < 409600 = 400/(1/1024)`.
The logarithmic hypothesis is automatic on an eventual tail. -/
theorem four_mul_lm43FarRadius_le_lmSimpleRadius
    {n : ℕ} (hn : 32 ≤ n)
    (hlog : (5 : ℝ) ≤ Real.log (n : ℝ)) :
    4 * lm43FarRadius n ≤ Parameters.lmSimpleRadius (1 / 1024) n := by
  let x := Real.log (n : ℝ)
  let C := lm43GrowthDenominator n
  let k := Nat.log 2 n
  let j := Nat.log 2 (lm43K n)
  have hx : (5 : ℝ) ≤ x := by simpa [x] using hlog
  have hxpos : 0 < x := by linarith
  have hxone : (1 : ℝ) ≤ x := by linarith
  have hClt : (C : ℝ) < 9216 * x ^ 2 + 1 := by
    dsimp [C, lm43GrowthDenominator, x]
    exact Nat.ceil_lt_add_one (by positivity)
  have hC : (C : ℝ) ≤ 9217 * x ^ 2 := by
    have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hxone
    linarith
  have hjk : j ≤ k := by
    dsimp [j, k]
    exact Nat.log_mono_right (Nat.div_le_self n 4)
  have hpowNat : 2 ^ k ≤ n := by
    exact Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hpowReal : (((2 ^ k : ℕ) : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast hpowNat
  have hlogPow : (k : ℝ) * Real.log 2 ≤ x := by
    have h := Real.log_le_log
      (by positivity : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ)) hpowReal
    simpa [x, Real.log_pow] using h
  have hlogTwo : (69 : ℝ) / 100 ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hjkReal : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
  have hkBound : 69 * (k : ℝ) ≤ 100 * x := by
    nlinarith
  have hfactor : (j : ℝ) + 1 ≤ (5 / 3 : ℝ) * x := by
    nlinarith
  have hfar : (lm43FarRadius n : ℝ) ≤ 46085 * x ^ 3 := by
    calc
      (lm43FarRadius n : ℝ) =
          3 * (C : ℝ) * ((j : ℝ) + 1) := by
        simp only [lm43FarRadius, lm43FreshRadius, lm43HalvingRounds,
          C, j, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      _ ≤ 3 * (9217 * x ^ 2) * ((j : ℝ) + 1) := by gcongr
      _ ≤ 3 * (9217 * x ^ 2) * ((5 / 3 : ℝ) * x) := by gcongr
      _ = 46085 * x ^ 3 := by ring
  have hs := Parameters.lmSimpleRadius_lower (1 / 1024 : ℝ) n
  have hreal : ((4 * lm43FarRadius n : ℕ) : ℝ) ≤
      (Parameters.lmSimpleRadius (1 / 1024) n : ℝ) := by
    push_cast
    calc
      (4 : ℝ) * lm43FarRadius n ≤ 4 * (46085 * x ^ 3) := by gcongr
      _ = 184340 * x ^ 3 := by ring
      _ ≤ 409600 * x ^ 3 := by
        nlinarith [pow_nonneg hxpos.le 3]
      _ = (400 / (1 / 1024 : ℝ)) * Real.log (n : ℝ) ^ 3 := by
        norm_num [x]
      _ ≤ (Parameters.lmSimpleRadius (1 / 1024) n : ℝ) := hs
  exact_mod_cast hreal

def lm315K (n : ℕ) : ℕ := n / 8

noncomputable def lm315FreshRadius (n : ℕ) : ℕ := 6 * lmGrowthDivisor n

def lm315HalvingRounds (n : ℕ) : ℕ := Nat.log 2 (lm315K n) + 1

def lm315HalvingCenters (n i : ℕ) : ℕ :=
  2 ^ (lm315HalvingRounds n - i)

noncomputable def lm315FreshWorkspace (n : ℕ) : ℕ :=
  lmGrowthGain n (lm315K n)

noncomputable def lm315RouteWorkspace (n : ℕ) : ℕ :=
  500 * Parameters.lmRadius (1 / 1024) n ^ 2

noncomputable def lm315PathWorkspace (n : ℕ) : ℕ :=
  Parameters.lmFloorEndpoint n + 2 * lm315RouteWorkspace n

noncomputable def lm315L (n : ℕ) : ℕ :=
  lmGrowthDivisor n * lm315PathWorkspace n

noncomputable def lm315RouteBase (n : ℕ) : ℕ :=
  lmGrowthDivisor n * lm315RouteWorkspace n

noncomputable def lm315RouteStart (n d : ℕ) : ℕ :=
  lmSeedStart d (lm315RouteBase n) (lm315RouteWorkspace n)

noncomputable def lm315PathStart (n d : ℕ) : ℕ :=
  lmSeedStart d (lm315L n) (lm315PathWorkspace n)

noncomputable def concreteHalvingSchedule (n : ℕ) :
    HalvingSchedule (lm315K n) (lm315HalvingRounds n) where
  centers := lm315HalvingCenters n
  zero := by
    have hlt : lm315K n < 2 ^ (Nat.log 2 (lm315K n) + 1) :=
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) (lm315K n)
    simpa [lm315HalvingCenters, lm315HalvingRounds] using hlt.le
  step := by
    intro i hi
    let q := lm315HalvingRounds n - (i + 1)
    have hexp : lm315HalvingRounds n - i = q + 1 := by
      dsimp [q]
      omega
    have hnext : lm315HalvingRounds n - (i + 1) = q := rfl
    simp only [lm315HalvingCenters, hexp, hnext, pow_succ]
    omega
  last := by simp [lm315HalvingCenters]

theorem lm315K_target {n : ℕ} (hn : 32 ≤ n)
    (hlarge : 2 * lmGrowthDivisor n ≤ lm315K n) :
    n / 2 + 1 ≤ lmGrowthCurve n (lm315K n) (lm315FreshRadius n) := by
  have hcurve := pow_mul_le_lmGrowthCurve_blocks
    (N := n) (D := lm315K n) (hn.trans' (by omega)) hlarge 3
  have hmod := Nat.mod_lt n (by omega : 0 < 8)
  have hdecomp := Nat.div_add_mod n 8
  have hhalf : n / 2 + 1 ≤ 8 * (n / 8) := by omega
  simpa [lm315FreshRadius, lm315K, pow_succ, mul_assoc, mul_comm, mul_left_comm]
    using hhalf.trans hcurve

/-- The four asymptotic inequalities from which every field and every bridge
budget of the concrete Corollary 3.15 package is derived. -/
structure LM315ScaleBounds (n : ℕ) : Prop where
  card_large : 32 ≤ n
  route_fits :
    lm315RouteBase n + lm315RouteWorkspace n ≤ Parameters.lmExpansionOrder n
  L_le_K : lm315L n ≤ lm315K n
  lemma13_fresh :
    220 * Parameters.lmRadius (1 / 1024) n ^ 2 +
        4 * Parameters.lmExpansionOrder n +
        (32 * Parameters.lmRadius (1 / 1024) n) * lm315L n ≤
      lm315FreshWorkspace n
  long_fresh :
    220 * Parameters.lmRadius (1 / 1024) n ^ 2 +
        Parameters.lmFloorEndpoint n +
        14 * Parameters.lmRadius (1 / 1024) n + 2 * lm315L n + 3 ≤
      lm315FreshWorkspace n

/-- The source parameter scales satisfy all four decisive estimates once the
ambient order is large.  The deliberately enormous logarithmic threshold
keeps the proof elementary: ceilings are bounded by one extra copy of the
relevant logarithmic monomial, and `log(n)^30 ≤ n` absorbs every purely
polylogarithmic remainder. -/
theorem eventually_lm315ScaleBounds :
    ∀ᶠ n : ℕ in Filter.atTop, LM315ScaleBounds n := by
  let A : ℝ := 1638401
  let B : ℝ := 18434
  let C : ℝ := 500 * A ^ 2
  let Q : ℝ := 10000000000000000000000000000000000000000
  have hlogtop : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogQ := hlogtop.eventually (Filter.eventually_ge_atTop Q)
  have hpow30 := tendsto_natCast_atTop_atTop.eventually
    (Parameters.eventually_log_pow_le_self 30)
  filter_upwards [Filter.eventually_ge_atTop 32, hlogQ, hpow30] with n hn hnQ hn30
  let x := Real.log (n : ℝ)
  let y : ℝ := n
  let m := Parameters.lmRadius (1 / 1024) n
  let D := Parameters.lmExpansionOrder n
  let P := Parameters.lmFloorEndpoint n
  let q := lmGrowthDenominator n
  let div := lmGrowthDivisor n
  let rw := lm315RouteWorkspace n
  let pw := lm315PathWorkspace n
  let L := lm315L n
  let K := lm315K n
  have hxQ : Q ≤ x := by simpa [x] using hnQ
  have hxone : (1 : ℝ) ≤ x := by
    exact (show (1 : ℝ) ≤ Q by norm_num [Q]).trans hxQ
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hypos : 0 < y := by
    dsimp [y]
    positivity
  have hx30 : x ^ 30 ≤ y := by simpa [x, y] using hn30
  have hQpow (k : ℕ) (hk : 1 ≤ k) : Q ≤ x ^ k := by
    exact hxQ.trans (by
      simpa only [pow_one] using pow_le_pow_right₀ hxone hk)
  have hq : (q : ℝ) ≤ 9217 * x ^ 2 := by
    have hlt : (q : ℝ) < 9216 * x ^ 2 + 1 := by
      simpa [q, lmGrowthDenominator, x] using
        (Nat.ceil_lt_add_one (by positivity : 0 ≤ 9216 * x ^ 2))
    have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hxone
    linarith
  have hdiv : (div : ℝ) ≤ B * x ^ 2 := by
    dsimp [div, lmGrowthDivisor, B]
    push_cast
    nlinarith
  have hdivpos : 0 < div :=
    lmGrowthDivisor_pos (hn.trans' (by omega))
  have hm : (m : ℝ) ≤ A * x ^ 3 := by
    have hlt := Parameters.lmRadius_lt_add_one
      (n := n) (show (0 : ℝ) < 1 / 1024 by norm_num)
    have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hxone
    dsimp [m, A, x] at hlt ⊢
    norm_num at hlt ⊢
    nlinarith
  have hDlow : x ^ 10 ≤ (D : ℝ) := by
    simpa [x, D] using Parameters.lmExpansionOrder_lower n
  have hDup : (D : ℝ) ≤ 2 * x ^ 10 := by
    simpa [x, D] using
      Parameters.lmExpansionOrder_le_two_mul (one_le_pow₀ hxone)
  have hscale : 0 ≤ Parameters.lmPathScale (n : ℝ) := by
    simp only [Parameters.lmPathScale]
    positivity
  have hP : (P : ℝ) ≤ y / x ^ 12 := by
    simpa [P, y, x, Parameters.lmPathScale] using
      Parameters.lmFloorEndpoint_le_pathScale n hscale
  have hrw : (rw : ℝ) ≤ C * x ^ 6 := by
    dsimp [rw, lm315RouteWorkspace, C]
    push_cast
    have hm2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (m : ℝ)) hm 2
    nlinarith [pow_nonneg hxpos.le]
  have hpw : (pw : ℝ) ≤ y / x ^ 12 + 2 * C * x ^ 6 := by
    dsimp [pw, lm315PathWorkspace]
    push_cast
    change (P : ℝ) + 2 * (rw : ℝ) ≤ y / x ^ 12 + 2 * C * x ^ 6
    have htwo : (0 : ℝ) ≤ 2 := by norm_num
    simpa [mul_assoc] using
      add_le_add hP (mul_le_mul_of_nonneg_left hrw htwo)
  have hL : (L : ℝ) ≤ B * y / x ^ 10 + 2 * B * C * x ^ 8 := by
    dsimp [L, lm315L]
    push_cast
    calc
      (div : ℝ) * (pw : ℝ)
          ≤ (B * x ^ 2) * (y / x ^ 12 + 2 * C * x ^ 6) := by
            exact mul_le_mul hdiv hpw (by positivity) (by positivity)
      _ = B * y / x ^ 10 + 2 * B * C * x ^ 8 := by
        field_simp [ne_of_gt hxpos]
        <;> ring
  have hrouteCoeff : (B + 1) * C ≤ x ^ 2 := by
    calc
      (B + 1) * C ≤ Q := by norm_num [A, B, C, Q]
      _ ≤ x ^ 2 := hQpow 2 (by omega)
  have hrouteUpper :
      ((lm315RouteBase n + lm315RouteWorkspace n : ℕ) : ℝ) ≤ x ^ 10 := by
    push_cast
    dsimp only [lm315RouteBase, lm315RouteWorkspace]
    push_cast
    have hdiv' : (lmGrowthDivisor n : ℝ) ≤ B * x ^ 2 := by
      simpa [div] using hdiv
    have hrw' : 500 * (Parameters.lmRadius (1 / 1024) n : ℝ) ^ 2 ≤
        C * x ^ 6 := by
      simpa [rw, lm315RouteWorkspace] using hrw
    calc
      (lmGrowthDivisor n : ℝ) *
            (500 * (Parameters.lmRadius (1 / 1024) n : ℝ) ^ 2) +
          500 * (Parameters.lmRadius (1 / 1024) n : ℝ) ^ 2
          ≤ (B * x ^ 2) * (C * x ^ 6) + C * x ^ 6 := by
            exact add_le_add (mul_le_mul hdiv' hrw' (by positivity) (by positivity)) hrw'
      _ ≤ ((B + 1) * C) * x ^ 8 := by
        have hx6x8 : x ^ 6 ≤ x ^ 8 := pow_le_pow_right₀ hxone (by omega)
        have hCnonneg : 0 ≤ C := by positivity
        calc
          (B * x ^ 2) * (C * x ^ 6) + C * x ^ 6
              = B * C * x ^ 8 + C * x ^ 6 := by ring
          _ ≤ B * C * x ^ 8 + C * x ^ 8 :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hx6x8 hCnonneg)
          _ = ((B + 1) * C) * x ^ 8 := by ring
      _ ≤ x ^ 2 * x ^ 8 :=
        mul_le_mul_of_nonneg_right hrouteCoeff (pow_nonneg hxpos.le 8)
      _ = x ^ 10 := by ring
  have hrouteFits :
      lm315RouteBase n + lm315RouteWorkspace n ≤ D := by
    exact_mod_cast hrouteUpper.trans hDlow
  have h16B : 16 * B ≤ x ^ 10 := by
    calc
      16 * B ≤ Q := by norm_num [B, Q]
      _ ≤ x ^ 10 := hQpow 10 (by omega)
  have h32BC : 32 * B * C ≤ x ^ 22 := by
    calc
      32 * B * C ≤ Q := by norm_num [A, B, C, Q]
      _ ≤ x ^ 22 := hQpow 22 (by omega)
  have hLfirst : 8 * (B * y / x ^ 10) ≤ y / 2 := by
    rw [show 8 * (B * y / x ^ 10) = (8 * B * y) / x ^ 10 by ring,
      div_le_iff₀ (pow_pos hxpos 10)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h16B) hypos.le]
  have hLsecond : 8 * (2 * B * C * x ^ 8) ≤ y / 2 := by
    have hpoly : 32 * B * C * x ^ 8 ≤ x ^ 30 := by
      calc
        32 * B * C * x ^ 8 ≤ x ^ 22 * x ^ 8 :=
          mul_le_mul_of_nonneg_right h32BC (pow_nonneg hxpos.le 8)
        _ = x ^ 30 := by ring
    calc
      8 * (2 * B * C * x ^ 8) = (32 * B * C * x ^ 8) / 2 := by ring
      _ ≤ y / 2 := div_le_div_of_nonneg_right (hpoly.trans hx30) (by norm_num)
  have h8L : 8 * (L : ℝ) ≤ y := by
    calc
      8 * (L : ℝ) ≤
          8 * (B * y / x ^ 10 + 2 * B * C * x ^ 8) :=
        mul_le_mul_of_nonneg_left hL (by norm_num)
      _ = 8 * (B * y / x ^ 10) + 8 * (2 * B * C * x ^ 8) := by ring
      _ ≤ y / 2 + y / 2 := add_le_add hLfirst hLsecond
      _ = y := by ring
  have hLK : L ≤ K := by
    dsimp [K, lm315K]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 8)).2
    have h8L' : (((L * 8 : ℕ) : ℝ)) ≤ (n : ℝ) := by
      push_cast
      simpa [y, mul_comm] using h8L
    exact_mod_cast h8L'
  have hpoly (coeff : ℝ) (power complement : ℕ)
      (hcomp : 1 ≤ complement) (hsum : power + complement = 30)
      (hcoeff : coeff ≤ Q) :
      coeff * x ^ power ≤ y := by
    calc
      coeff * x ^ power ≤ x ^ complement * x ^ power :=
        mul_le_mul_of_nonneg_right
          (hcoeff.trans (hQpow complement hcomp)) (pow_nonneg hxpos.le power)
      _ = x ^ 30 := by
        rw [← pow_add, show complement + power = 30 by omega]
      _ ≤ y := hx30
  have ht1 : 1760 * A ^ 2 * B * x ^ 8 ≤ y / 8 := by
    have := hpoly (14080 * A ^ 2 * B) 8 22 (by omega) (by omega)
      (by norm_num [A, B, Q])
    linarith only [this]
  have ht2 : 64 * B * x ^ 12 ≤ y / 8 := by
    have := hpoly (512 * B) 12 18 (by omega) (by omega)
      (by norm_num [B, Q])
    linarith only [this]
  have ht3 : 256 * A * B ^ 2 * y / x ^ 5 ≤ y / 2 := by
    have hcoef : 512 * A * B ^ 2 ≤ x ^ 5 := by
      exact (show 512 * A * B ^ 2 ≤ Q by norm_num [A, B, Q]).trans
        (hQpow 5 (by omega))
    rw [div_le_iff₀ (pow_pos hxpos 5)]
    have hmul := mul_le_mul_of_nonneg_right hcoef hypos.le
    nlinarith only [hmul]
  have ht4 : 512 * A * B ^ 2 * C * x ^ 13 ≤ y / 4 := by
    have := hpoly (2048 * A * B ^ 2 * C) 13 17 (by omega) (by omega)
      (by norm_num [A, B, C, Q])
    linarith only [this]
  let F₁ := 220 * m ^ 2 + 4 * D + (32 * m) * L
  have hF₁ : (8 : ℝ) * (F₁ : ℝ) * (div : ℝ) ≤ y := by
    have hm2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (m : ℝ)) hm 2
    have hm2' : (m : ℝ) ^ 2 ≤ A ^ 2 * x ^ 6 := by
      calc
        (m : ℝ) ^ 2 ≤ (A * x ^ 3) ^ 2 := hm2
        _ = A ^ 2 * x ^ 6 := by ring
    have hmL : (m : ℝ) * (L : ℝ) ≤
        A * x ^ 3 * (B * y / x ^ 10 + 2 * B * C * x ^ 8) :=
      mul_le_mul hm hL (by positivity) (by positivity)
    have hFupper : (F₁ : ℝ) ≤
        220 * A ^ 2 * x ^ 6 + 8 * x ^ 10 +
          32 * A * x ^ 3 * (B * y / x ^ 10 + 2 * B * C * x ^ 8) := by
      dsimp [F₁]
      push_cast
      have h220 := mul_le_mul_of_nonneg_left hm2' (by norm_num : (0 : ℝ) ≤ 220)
      have hfour := mul_le_mul_of_nonneg_left hDup (by norm_num : (0 : ℝ) ≤ 4)
      have hthirtyTwo :=
        mul_le_mul_of_nonneg_left hmL (by norm_num : (0 : ℝ) ≤ 32)
      calc
        220 * (m : ℝ) ^ 2 + 4 * (D : ℝ) + 32 * (m : ℝ) * (L : ℝ)
            ≤ 220 * (A ^ 2 * x ^ 6) + 4 * (2 * x ^ 10) +
                32 * (A * x ^ 3 *
                  (B * y / x ^ 10 + 2 * B * C * x ^ 8)) := by
              exact add_le_add (add_le_add h220 hfour)
                (by simpa [mul_assoc] using hthirtyTwo)
        _ = 220 * A ^ 2 * x ^ 6 + 8 * x ^ 10 +
              32 * A * x ^ 3 *
                (B * y / x ^ 10 + 2 * B * C * x ^ 8) := by ring
    calc
      (8 : ℝ) * (F₁ : ℝ) * (div : ℝ)
          ≤ 8 * (220 * A ^ 2 * x ^ 6 + 8 * x ^ 10 +
              32 * A * x ^ 3 *
                (B * y / x ^ 10 + 2 * B * C * x ^ 8)) *
              (B * x ^ 2) := by gcongr
      _ = 1760 * A ^ 2 * B * x ^ 8 + 64 * B * x ^ 12 +
          256 * A * B ^ 2 * y / x ^ 5 +
          512 * A * B ^ 2 * C * x ^ 13 := by
            field_simp [ne_of_gt hxpos]
            <;> ring
      _ ≤ y := by linarith only [ht1, ht2, ht3, ht4]
  have hF₁K : F₁ * div ≤ K := by
    dsimp [K, lm315K]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 8)).2
    have hF₁' : ((((F₁ * div) * 8 : ℕ) : ℝ)) ≤ (n : ℝ) := by
      push_cast
      simpa [y, mul_comm, mul_left_comm, mul_assoc] using hF₁
    exact_mod_cast hF₁'
  have hF₁fresh : F₁ ≤ lm315FreshWorkspace n := by
    rw [lm315FreshWorkspace, lmGrowthGain]
    exact (Nat.le_div_iff_mul_le hdivpos).2 hF₁K
  have hs1 : 1760 * A ^ 2 * B * x ^ 8 ≤ y / 8 := ht1
  have hs2 : 8 * B * y / x ^ 10 ≤ y / 8 := by
    have hcoef : 64 * B ≤ x ^ 10 :=
      (show 64 * B ≤ Q by norm_num [B, Q]).trans (hQpow 10 (by omega))
    rw [div_le_iff₀ (pow_pos hxpos 10)]
    have hmul := mul_le_mul_of_nonneg_right hcoef hypos.le
    nlinarith only [hmul]
  have hs3 : 112 * A * B * x ^ 5 ≤ y / 8 := by
    have := hpoly (896 * A * B) 5 25 (by omega) (by omega)
      (by norm_num [A, B, Q])
    linarith only [this]
  have hs4 : 16 * B ^ 2 * y / x ^ 8 ≤ y / 4 := by
    have hcoef : 64 * B ^ 2 ≤ x ^ 8 :=
      (show 64 * B ^ 2 ≤ Q by norm_num [B, Q]).trans (hQpow 8 (by omega))
    rw [div_le_iff₀ (pow_pos hxpos 8)]
    have hmul := mul_le_mul_of_nonneg_right hcoef hypos.le
    nlinarith only [hmul]
  have hs5 : 32 * B ^ 2 * C * x ^ 10 ≤ y / 8 := by
    have := hpoly (256 * B ^ 2 * C) 10 20 (by omega) (by omega)
      (by norm_num [A, B, C, Q])
    linarith only [this]
  have hs6 : 24 * B * x ^ 2 ≤ y / 8 := by
    have := hpoly (192 * B) 2 28 (by omega) (by omega)
      (by norm_num [B, Q])
    linarith only [this]
  let F₂ := 220 * m ^ 2 + P + 14 * m + 2 * L + 3
  have hF₂ : (8 : ℝ) * (F₂ : ℝ) * (div : ℝ) ≤ y := by
    have hm2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (m : ℝ)) hm 2
    have hm2' : (m : ℝ) ^ 2 ≤ A ^ 2 * x ^ 6 := by
      calc
        (m : ℝ) ^ 2 ≤ (A * x ^ 3) ^ 2 := hm2
        _ = A ^ 2 * x ^ 6 := by ring
    have hFupper : (F₂ : ℝ) ≤
        220 * A ^ 2 * x ^ 6 + y / x ^ 12 + 14 * A * x ^ 3 +
          2 * (B * y / x ^ 10 + 2 * B * C * x ^ 8) + 3 := by
      dsimp [F₂]
      push_cast
      have h220 := mul_le_mul_of_nonneg_left hm2' (by norm_num : (0 : ℝ) ≤ 220)
      have hfourteen := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 14)
      have htwoL := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 2)
      calc
        220 * (m : ℝ) ^ 2 + (P : ℝ) + 14 * (m : ℝ) +
              2 * (L : ℝ) + 3
            ≤ 220 * (A ^ 2 * x ^ 6) + y / x ^ 12 +
                14 * (A * x ^ 3) +
                2 * (B * y / x ^ 10 + 2 * B * C * x ^ 8) + 3 := by
              exact add_le_add
                (add_le_add
                  (add_le_add (add_le_add h220 hP) hfourteen) htwoL)
                le_rfl
        _ = 220 * A ^ 2 * x ^ 6 + y / x ^ 12 + 14 * A * x ^ 3 +
              2 * (B * y / x ^ 10 + 2 * B * C * x ^ 8) + 3 := by ring
    calc
      (8 : ℝ) * (F₂ : ℝ) * (div : ℝ)
          ≤ 8 * (220 * A ^ 2 * x ^ 6 + y / x ^ 12 +
              14 * A * x ^ 3 +
              2 * (B * y / x ^ 10 + 2 * B * C * x ^ 8) + 3) *
              (B * x ^ 2) := by gcongr
      _ = 1760 * A ^ 2 * B * x ^ 8 + 8 * B * y / x ^ 10 +
          112 * A * B * x ^ 5 + 16 * B ^ 2 * y / x ^ 8 +
          32 * B ^ 2 * C * x ^ 10 + 24 * B * x ^ 2 := by
            field_simp [ne_of_gt hxpos]
            <;> ring
      _ ≤ y := by linarith only [hs1, hs2, hs3, hs4, hs5, hs6, hypos.le]
  have hF₂K : F₂ * div ≤ K := by
    dsimp [K, lm315K]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 8)).2
    have hF₂' : ((((F₂ * div) * 8 : ℕ) : ℝ)) ≤ (n : ℝ) := by
      push_cast
      simpa [y, mul_comm, mul_left_comm, mul_assoc] using hF₂
    exact_mod_cast hF₂'
  have hF₂fresh : F₂ ≤ lm315FreshWorkspace n := by
    rw [lm315FreshWorkspace, lmGrowthGain]
    exact (Nat.le_div_iff_mul_le hdivpos).2 hF₂K
  exact
    { card_large := hn
      route_fits := by simpa [D] using hrouteFits
      L_le_K := by simpa [L, K] using hLK
      lemma13_fresh := by simpa [F₁, m, D, L] using hF₁fresh
      long_fresh := by simpa [F₂, m, P, L] using hF₂fresh }

/-- A concrete, schedule-free Corollary 3.15 certificate, including the four
uniform bridge estimates used by the exact-path assembler. -/
structure LM315ConcreteData [Fintype V] (G : SimpleGraph V) (d : ℕ) where
  numerics : LM315Numerics G (1 / 1024) ((1 / 64) * (d : ℝ))
    (Parameters.lmExpansionOrder (Fintype.card V))
    (lm315K (Fintype.card V)) (lm315L (Fintype.card V))
    (Parameters.lmRadius (1 / 1024) (Fintype.card V))
    (lm315FreshRadius (Fintype.card V)) (lmGrowthRounds (Fintype.card V))
    (lm315HalvingRounds (Fintype.card V))
    (lm315FreshWorkspace (Fintype.card V))
    (lm315PathWorkspace (Fintype.card V))
  degreeScale_eq : numerics.degreeScale = d
  lemma13_fresh :
    220 * Parameters.lmRadius (1 / 1024) (Fintype.card V) ^ 2 +
        4 * Parameters.lmExpansionOrder (Fintype.card V) +
        (32 * Parameters.lmRadius (1 / 1024) (Fintype.card V)) *
          lm315L (Fintype.card V) ≤ lm315FreshWorkspace (Fintype.card V)
  lemma13_route :
    220 * Parameters.lmRadius (1 / 1024) (Fintype.card V) ^ 2 +
        (8 * Parameters.lmRadius (1 / 1024) (Fintype.card V)) *
          (7 * Parameters.lmRadius (1 / 1024) (Fintype.card V) + 4) ≤
      numerics.routeWorkspace
  long_fresh : ∀ ell : ℕ,
    (ell : ℝ) ≤ Parameters.lmPathScale (Fintype.card V : ℝ) →
      220 * Parameters.lmRadius (1 / 1024) (Fintype.card V) ^ 2 + ell +
          14 * Parameters.lmRadius (1 / 1024) (Fintype.card V) +
          2 * lm315L (Fintype.card V) + 3 ≤
        lm315FreshWorkspace (Fintype.card V)
  long_path : ∀ ell : ℕ,
    (ell : ℝ) ≤ Parameters.lmPathScale (Fintype.card V : ℝ) →
      220 * Parameters.lmRadius (1 / 1024) (Fintype.card V) ^ 2 + ell +
          14 * Parameters.lmRadius (1 / 1024) (Fintype.card V) + 3 ≤
        lm315PathWorkspace (Fintype.card V)

/-- Construct the full numerical package from the four eventual scale
inequalities.  The only use of `d ≤ n` is the bulk `K=n/8` seed; all small
endpoint seeds use the direct-or-bootstrap alternative. -/
noncomputable def lm315ConcreteDataOfBounds
    [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (hd : 1 ≤ d) (hdn : d ≤ Fintype.card V)
    (H : LM315ScaleBounds (Fintype.card V)) : LM315ConcreteData G d := by
  let n := Fintype.card V
  let D := Parameters.lmExpansionOrder n
  let m := Parameters.lmRadius (1 / 1024) n
  let div := lmGrowthDivisor n
  let routeW := lm315RouteWorkspace n
  let pathW := lm315PathWorkspace n
  let routeBase := lm315RouteBase n
  let L := lm315L n
  let K := lm315K n
  let freshW := lm315FreshWorkspace n
  have hnlarge : 32 ≤ n := by simpa [n] using H.card_large
  have hdivpos : 0 < div := lmGrowthDivisor_pos (H.card_large.trans' (by omega))
  have hdivone : 1 ≤ div := hdivpos
  have hmpos : 0 < m := by
    apply Nat.ceil_pos.mpr
    have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    exact mul_pos (by norm_num) (pow_pos (Real.log_pos hnreal) 3)
  have hDpos : 0 < D := Parameters.lmExpansionOrder_pos (show 1 < n by omega)
  have hrouteWpos : 0 < routeW := by
    dsimp [routeW, lm315RouteWorkspace]
    positivity
  have hrouteWtwo : 2 ≤ routeW := by
    have hmone : 1 ≤ m := hmpos
    dsimp [routeW, lm315RouteWorkspace]
    nlinarith [one_le_pow₀ (n := 2) hmone]
  have hpathWpos : 0 < pathW := by
    dsimp [pathW, lm315PathWorkspace]
    omega
  have hrouteWBase : routeW ≤ routeBase := by
    dsimp [routeBase, lm315RouteBase]
    simpa only [one_mul] using Nat.mul_le_mul_right routeW hdivone
  have hpathWL : pathW ≤ L := by
    dsimp [L, lm315L]
    simpa only [one_mul] using Nat.mul_le_mul_right pathW hdivone
  have hrouteLarge : 2 * div ≤ routeBase := by
    dsimp [routeBase, lm315RouteBase]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left div hrouteWtwo
  have hrouteTarget : routeBase + routeW ≤ L := by
    have hrwpw : 2 * routeW ≤ pathW := by
      dsimp [pathW, lm315PathWorkspace]
      omega
    have hmul := Nat.mul_le_mul_left div hrwpw
    have hwMul : routeW ≤ div * routeW := by
      simpa only [one_mul] using Nat.mul_le_mul_right routeW hdivone
    dsimp [routeBase, lm315RouteBase, L, lm315L]
    calc
      div * routeW + routeW ≤ div * routeW + div * routeW :=
        Nat.add_le_add_left hwMul _
      _ = div * (2 * routeW) := by ring
      _ ≤ div * pathW := hmul
  have hLpos : 0 < L := hpathWpos.trans_le hpathWL
  have hKpos : 0 < K := hLpos.trans_le H.L_le_K
  have hKlarge : 2 * div ≤ K :=
    hrouteLarge.trans ((Nat.le_add_right routeBase routeW).trans
      (hrouteTarget.trans H.L_le_K))
  have hrouteGain : routeW ≤ lmGrowthGain n routeBase := by
    change routeW ≤ (div * routeW) / div
    simpa [Nat.mul_comm] using (Nat.mul_div_left routeW hdivpos).ge
  have hpathGain : pathW ≤ lmGrowthGain n L := by
    change pathW ≤ (div * pathW) / div
    simpa [Nat.mul_comm] using (Nat.mul_div_left pathW hdivpos).ge
  have hrouteBaseStart : routeBase ≤ lm315RouteStart n d :=
    lmSeedStart_base_le hrouteWBase
  have hpathBaseStart : L ≤ lm315PathStart n d :=
    lmSeedStart_base_le hpathWL
  have hrouteCutoff : (d : ℝ) / 128 ≤ (lm315RouteStart n d : ℝ) :=
    lmSeedStart_cutoff hrouteWBase
  have hpathCutoff : (d : ℝ) / 128 ≤ (lm315PathStart n d : ℝ) :=
    lmSeedStart_cutoff hpathWL
  have hrouteStartGain : routeW ≤ lmGrowthGain n (lm315RouteStart n d) :=
    hrouteGain.trans (lmGrowthGain_mono n hrouteBaseStart)
  have hpathStartGain : pathW ≤ lmGrowthGain n (lm315PathStart n d) :=
    hpathGain.trans (lmGrowthGain_mono n hpathBaseStart)
  have hrouteStartLarge : 2 * div ≤ lm315RouteStart n d :=
    hrouteLarge.trans hrouteBaseStart
  have hpathStartLarge : 2 * div ≤ lm315PathStart n d :=
    hrouteLarge.trans ((Nat.le_add_right routeBase routeW).trans
      (hrouteTarget.trans hpathBaseStart))
  have hKcutoff : (d : ℝ) / 128 ≤ (K : ℝ) := by
    have hreal : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
    have hnK : n ≤ 16 * K := by
      have hnlarge := H.card_large
      have hmod := Nat.mod_lt n (by omega : 0 < 8)
      have hdecomp := Nat.div_add_mod n 8
      dsimp [K, lm315K]
      omega
    have hnKreal : (n : ℝ) ≤ 16 * (K : ℝ) := by exact_mod_cast hnK
    linarith
  have hfreshRoom : freshW + K ≤ n := by
    have hfreshK : freshW ≤ K := by
      dsimp [freshW, lm315FreshWorkspace, lmGrowthGain]
      exact Nat.div_le_self _ _
    have htwoK : 2 * K ≤ n := by
      dsimp [K, lm315K]
      omega
    omega
  have hhalve : 2 * K ≤ n / 2 + 1 := by
    dsimp [K, lm315K]
    omega
  have hlogK : Nat.log 2 K ≤ Nat.log 2 n :=
    Nat.log_mono_right (Nat.div_le_self n 8)
  have hfreshRadius :
      2 * (lm315FreshRadius n * lm315HalvingRounds n) ≤ m := by
    have hlogK' : Nat.log 2 K + 1 ≤ Nat.log 2 n + 1 := by omega
    have hmulLog := Nat.mul_le_mul_left (12 * div) hlogK'
    have hsix :
        2 * (lm315FreshRadius n * lm315HalvingRounds n) ≤
          6 * lmGrowthRounds n := by
      dsimp [lm315FreshRadius, lm315HalvingRounds, lmGrowthRounds]
      dsimp [K] at hmulLog
      nlinarith
    have hsixSeven : 6 * lmGrowthRounds n ≤ 7 * lmGrowthRounds n := by omega
    exact hsix.trans (hsixSeven.trans
      (seven_mul_lmGrowthRounds_le_lmRadius H.card_large))
  have hconnector : 2 * (lmGrowthRounds n + 1) ≤ m := by
    have hroundpos : 1 ≤ lmGrowthRounds n := by
      have hdivpos' := lmGrowthDivisor_pos (H.card_large.trans' (by omega))
      dsimp [lmGrowthRounds]
      exact Nat.mul_pos (Nat.mul_pos (by omega) hdivpos') (by omega)
    have : 2 * (lmGrowthRounds n + 1) ≤ 7 * lmGrowthRounds n := by omega
    exact this.trans (seven_mul_lmGrowthRounds_le_lmRadius H.card_large)
  have hrouteSourceSurvives : 1 + routeW ≤ D := by
    have hbasepos : 0 < routeBase := hrouteWpos.trans_le hrouteWBase
    have hfits : routeBase + routeW ≤ D := by
      simpa [routeBase, routeW, D] using H.route_fits
    omega
  have hrouteTargetSurvives : 1 + routeW ≤ L := by
    have hbasepos : 0 < routeBase := hrouteWpos.trans_le hrouteWBase
    omega
  have hrouteSourceSeed :
      lm315RouteStart n d + routeW ≤ D ∨
        lm315RouteStart n d + routeW ≤ d := by
    rcases lmSeedStart_direct_or_bootstrap hrouteWBase with h | h
    · exact Or.inl ((Nat.add_le_add_right h routeW).trans H.route_fits)
    · exact Or.inr h
  have hrouteTargetSeed :
      lm315RouteStart n d + routeW ≤ L ∨
        lm315RouteStart n d + routeW ≤ d := by
    rcases lmSeedStart_direct_or_bootstrap hrouteWBase with h | h
    · exact Or.inl ((Nat.add_le_add_right h routeW).trans hrouteTarget)
    · exact Or.inr h
  have hpathSeed : lm315PathStart n d ≤ L ∨
      lm315PathStart n d + pathW ≤ d :=
    lmSeedStart_direct_or_bootstrap hpathWL
  let N : LM315Numerics G (1 / 1024) ((1 / 64) * (d : ℝ)) D K L m
      (lm315FreshRadius n) (lmGrowthRounds n) (lm315HalvingRounds n)
      freshW pathW :=
    { routeStart := lm315RouteStart n d
      degreeScale := d
      pathStart := lm315PathStart n d
      routeWorkspace := routeW
      schedule := concreteHalvingSchedule n
      room := hfreshRoom
      D_pos := hDpos
      K_pos := hKpos
      L_pos := hLpos
      m_pos := hmpos
      routeStart_pos := hrouteWpos.trans_le
        (hrouteWBase.trans hrouteBaseStart)
      L_le_K := H.L_le_K
      growth_path := concreteBallGrowthSchedule G d (lm315PathStart n d) pathW
        H.card_large hd hpathCutoff hpathStartLarge hpathStartGain
      growth_route := concreteBallGrowthSchedule G d (lm315RouteStart n d) routeW
        H.card_large hd hrouteCutoff hrouteStartLarge hrouteStartGain
      growth_K := concreteBallGrowthScheduleOfTarget G d K freshW
        (lm315FreshRadius n) H.card_large hd hKcutoff le_rfl
          (lm315K_target H.card_large hKlarge)
      route_source_survives := hrouteSourceSurvives
      route_target_survives := hrouteTargetSurvives
      route_source_seed := hrouteSourceSeed
      route_target_seed := hrouteTargetSeed
      path_seed := hpathSeed
      halve := hhalve
      fresh_radius := hfreshRadius
      connector_radius := hconnector }
  have hrouteBudget :
      220 * m ^ 2 + (8 * m) * (7 * m + 4) ≤ routeW := by
    dsimp [routeW, lm315RouteWorkspace]
    have hmone : 1 ≤ m := hmpos
    have hmm : m ≤ m ^ 2 := by
      calc
        m = m * 1 := by simp
        _ ≤ m * m := Nat.mul_le_mul_left m hmone
        _ = m ^ 2 := by ring
    nlinarith
  have hscale : 0 ≤ Parameters.lmPathScale (n : ℝ) := by
    simp only [Parameters.lmPathScale]
    positivity
  have hellFloor : ∀ ell : ℕ,
      (ell : ℝ) ≤ Parameters.lmPathScale (n : ℝ) →
        ell ≤ Parameters.lmFloorEndpoint n := by
    intro ell hell
    exact Nat.le_floor hell
  have hlongPath : ∀ ell : ℕ,
      (ell : ℝ) ≤ Parameters.lmPathScale (n : ℝ) →
        220 * m ^ 2 + ell + 14 * m + 3 ≤ pathW := by
    intro ell hell
    have hellP := hellFloor ell hell
    dsimp [pathW, lm315PathWorkspace, routeW, lm315RouteWorkspace]
    have hmone : 1 ≤ m := hmpos
    have hmm : m ≤ m ^ 2 := by
      calc
        m = m * 1 := by simp
        _ ≤ m * m := Nat.mul_le_mul_left m hmone
        _ = m ^ 2 := by ring
    have hone : 1 ≤ m ^ 2 := one_le_pow₀ hmone
    have hfourteen : 14 * m ≤ 14 * m ^ 2 := Nat.mul_le_mul_left 14 hmm
    have hthree : 3 ≤ 3 * m ^ 2 := by
      simpa only [one_mul] using Nat.mul_le_mul_left 3 hone
    have hsmall : 220 * m ^ 2 + 14 * m + 3 ≤ 1000 * m ^ 2 := by omega
    change 220 * m ^ 2 + ell + 14 * m + 3 ≤
      Parameters.lmFloorEndpoint n + 2 * (500 * m ^ 2)
    omega
  refine
    { numerics := N
      degreeScale_eq := by simp [N]
      lemma13_fresh := by simpa [n, D, m, L, freshW] using H.lemma13_fresh
      lemma13_route := by simpa [N, n, m, routeW] using hrouteBudget
      long_fresh := ?_
      long_path := ?_ }
  · intro ell hell
    have hellP := hellFloor ell hell
    have hbase : 220 * m ^ 2 + Parameters.lmFloorEndpoint n + 14 * m +
        2 * L + 3 ≤ freshW := by
      simpa [n, m, L, freshW] using H.long_fresh
    simpa [n, m, L, freshW] using (show
      220 * m ^ 2 + ell + 14 * m + 2 * L + 3 ≤ freshW by omega)
  · intro ell hell
    simpa [n, m, pathW] using hlongPath ell hell

/-- Uniform eventual constructor requested by the exact-path assembler.  It
works for every positive `d ≤ n`; the package itself records `degreeScale=d`,
and downstream graph lemmas supply the genuine minimum-degree hypothesis. -/
theorem eventually_exists_lm315Numerics :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ d : ℕ, 1 ≤ d → d ≤ n →
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
        Fintype.card V = n → Nonempty (LM315ConcreteData G d) := by
  filter_upwards [eventually_lm315ScaleBounds] with n hn
  intro d hd hdn V inst G hcard
  subst n
  exact ⟨lm315ConcreteDataOfBounds G d hd hdn hn⟩

/-! ## Limited-contact growth, without paying for the retained set -/

/-- The concrete curve grows past half while avoiding `X ∪ Y ∪ Z`.
Only `X.card + Y.card` is paid globally; `Z` is charged through the
limited-contact estimate. -/
theorem half_le_ball_of_lmLimitedContact
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d D core contact : ℕ)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (A X Y Z : Finset V)
    (hN : 32 ≤ Fintype.card V) (hd : 1 ≤ d)
    (hAcard : D ≤ A.card)
    (hcutoff : (d : ℝ) / 128 ≤ (D : ℝ))
    (hlarge : 2 * lmGrowthDivisor (Fintype.card V) ≤ D)
    (hcore : X.card + Y.card ≤ core)
    (hcontactBudget :
      core + contact * lmGrowthRounds (Fintype.card V) ≤
        lmGrowthGain (Fintype.card V) D)
    (hAZ : ∀ a ∈ A, a ∉ Z)
    (hcontact : HasLimitedContact G A (Z : Set V) contact) :
    Fintype.card V / 2 + 1 ≤
      (ballAvoidingFrom G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A
          (lmGrowthRounds (Fintype.card V))).card := by
  let N := Fintype.card V
  let R := lmGrowthRounds N
  let curve := lmGrowthCurve N D
  let cap := N / 2 + 1
  have hind : ∀ i ≤ R,
      min (curve i) cap ≤
        (ballAvoidingFrom G
          ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A i).card := by
    intro i
    induction i with
    | zero =>
        intro _hi
        exact (min_le_left _ _).trans <| (by
          simpa [curve] using hAcard.trans <|
            Finset.card_le_card
              (subset_ballAvoidingFrom G
                ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A 0))
    | succ i ih =>
        intro hi
        have ih := ih (Nat.le_trans (Nat.le_succ i) hi)
        let F : Set V := (X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)
        let current := ballAvoidingFrom G F A i
        by_cases hcap : cap ≤ current.card
        · exact (min_le_right _ cap).trans <| hcap.trans <|
            Finset.card_le_card <|
              ballAvoidingFrom_radius_mono G F A (Nat.le_succ i)
        · have hcurrentUpper : current.card ≤ N / 2 := by
            dsimp [cap] at hcap
            omega
          have hcurveCurrent : curve i ≤ current.card := by
            by_contra hnot
            have hcapCurve : cap ≤ curve i := by
              by_contra hnotcap
              have : curve i < cap := Nat.lt_of_not_ge hnotcap
              have hle : curve i ≤ current.card := by
                simpa [min_eq_left (Nat.le_of_lt this), current, F] using ih
              exact hnot hle
            have : cap ≤ current.card := by
              simpa [min_eq_right hcapCurve, current, F] using ih
            exact hcap this
          let q := curve (i + 1) - current.card
          have hDcurrent : D ≤ current.card :=
            (lmGrowthCurve_start_le N D i).trans hcurveCurrent
          have hlower : ((1 / 64 : ℝ) * (d : ℝ)) / 2 ≤
              (current.card : ℝ) := by
            have hDreal : (D : ℝ) ≤ (current.card : ℝ) := by
              exact_mod_cast hDcurrent
            calc
              ((1 / 64 : ℝ) * (d : ℝ)) / 2 = (d : ℝ) / 128 := by ring
              _ ≤ (D : ℝ) := hcutoff
              _ ≤ _ := hDreal
          have hupper : (current.card : ℝ) ≤ (N : ℝ) / 2 := by
            have hupper' : (current.card : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by
              exact_mod_cast hcurrentUpper
            exact hupper'.trans Nat.cast_div_le
          have hq : q ≤ lmGrowthGain N current.card := by
            dsimp [q, curve]
            change lmGrowthCurve N D i ≤ current.card at hcurveCurrent
            have hgain := lmGrowthGain_mono N hcurveCurrent
            have hsub :
                lmGrowthCurve N D i + lmGrowthGain N (lmGrowthCurve N D i) -
                    current.card ≤ lmGrowthGain N (lmGrowthCurve N D i) := by
              omega
            exact hsub.trans hgain
          have hcontactRound : contact * (i + 1) ≤ contact * R := by
            exact Nat.mul_le_mul_left contact hi
          have hlossD : X.card + Y.card + contact * (i + 1) ≤
              lmGrowthGain N D := by
            have hcontactRound' : contact * (i + 1) ≤
                contact * lmGrowthRounds (Fintype.card V) := by
              simpa [R, N] using hcontactRound
            have hloss' : X.card + Y.card + contact * (i + 1) ≤
                core + contact * lmGrowthRounds (Fintype.card V) := by
              exact Nat.add_le_add hcore hcontactRound'
            exact hloss'.trans (by simpa [N] using hcontactBudget)
          have hloss : X.card + Y.card + contact * (i + 1) ≤
              lmGrowthGain N current.card :=
            hlossD.trans (lmGrowthGain_mono N hDcurrent)
          have hbudgetNat :
              q + X.card + Y.card + contact * (i + 1) ≤
                2 * lmGrowthGain N current.card := by
            omega
          have hbudget :
              ((q + X.card + Y.card + contact * (i + 1) : ℕ) : ℝ) ≤
                expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ))
                  current.card * (current.card : ℝ) := by
            have hbudgetReal :
                ((q + X.card + Y.card + contact * (i + 1) : ℕ) : ℝ) ≤
                  ((2 * lmGrowthGain N current.card : ℕ) : ℝ) := by
              exact_mod_cast hbudgetNat
            exact hbudgetReal.trans <|
              two_lmGrowthGain_le_expansion hN hd
                (hcutoff.trans (by exact_mod_cast hDcurrent))
                (hcurrentUpper.trans (Nat.div_le_self N 2))
          have hstep := hexp.card_ballAvoidingFrom_union_three_add_le_succ_of_limitedContact
            A X Y Z i q contact hAZ hcontact hlower hupper hbudget
          have htarget : curve (i + 1) ≤
              (ballAvoidingFrom G F A (i + 1)).card := by
            have hstep' : current.card + q ≤
                (ballAvoidingFrom G F A (i + 1)).card := by
              simpa [F, current] using hstep
            rcases le_total (curve (i + 1)) current.card with hle | hle
            · exact hle.trans (hstep'.trans' (Nat.le_add_right current.card q))
            · have heq : current.card + q = curve (i + 1) := by
                dsimp [q]
                exact Nat.add_sub_of_le hle
              simpa [heq] using hstep'
          exact (min_le_left _ cap).trans htarget
  have hlast := hind R le_rfl
  have htarget := lmGrowthCurve_reaches_half hN hlarge
  rw [min_eq_right htarget] at hlast
  simpa [R, cap] using hlast

/-- Two limited-contact balls grown with the same forbidden decomposition
intersect, producing the short connector used by Lemmas 3.4 and 4.7. -/
theorem exists_avoiding_path_between_of_lmLimitedContact
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d D core contact : ℕ)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (A B X Y Z : Finset V)
    (hN : 32 ≤ Fintype.card V) (hd : 1 ≤ d)
    (hAcard : D ≤ A.card) (hBcard : D ≤ B.card)
    (hcutoff : (d : ℝ) / 128 ≤ (D : ℝ))
    (hlarge : 2 * lmGrowthDivisor (Fintype.card V) ≤ D)
    (hcore : X.card + Y.card ≤ core)
    (hcontactBudget :
      core + contact * lmGrowthRounds (Fintype.card V) ≤
        lmGrowthGain (Fintype.card V) D)
    (hAZ : ∀ a ∈ A, a ∉ Z) (hBZ : ∀ b ∈ B, b ∉ Z)
    (hcontactA : HasLimitedContact G A (Z : Set V) contact)
    (hcontactB : HasLimitedContact G B (Z : Set V) contact) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsAvoidingPath
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) ({a, b} : Set V) ∧
        p.length ≤ 2 * lmGrowthRounds (Fintype.card V) := by
  have hAhalf := half_le_ball_of_lmLimitedContact G d D core contact hexp
    A X Y Z hN hd hAcard hcutoff hlarge hcore hcontactBudget hAZ hcontactA
  have hBhalf := half_le_ball_of_lmLimitedContact G d D core contact hexp
    B X Y Z hN hd hBcard hcutoff hlarge hcore hcontactBudget hBZ hcontactB
  have hsum : Fintype.card V <
      (ballAvoidingFrom G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A
          (lmGrowthRounds (Fintype.card V))).card +
      (ballAvoidingFrom G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) B
          (lmGrowthRounds (Fintype.card V))).card := by omega
  simpa [two_mul] using exists_avoiding_path_between_of_large_balls G
    ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A B
      (lmGrowthRounds (Fintype.card V)) (lmGrowthRounds (Fintype.card V)) hsum

/-- The specialization used by the corrected adjuster join: the seed on
each side is the union of both ends, while only the ambient forbidden set and
the two small cores are deleted. -/
theorem exists_avoiding_path_between_of_lmSmallDeletion
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d D workspace : ℕ)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (W A B : Finset V)
    (hN : 32 ≤ Fintype.card V) (hd : 1 ≤ d)
    (hAcard : D ≤ A.card) (hBcard : D ≤ B.card)
    (hcutoff : (d : ℝ) / 128 ≤ (D : ℝ))
    (hlarge : 2 * lmGrowthDivisor (Fintype.card V) ≤ D)
    (hW : W.card ≤ workspace)
    (hworkspace : workspace ≤ lmGrowthGain (Fintype.card V) D) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsAvoidingPath (W : Set V) ({a, b} : Set V) ∧
        p.length ≤ 2 * lmGrowthRounds (Fintype.card V) := by
  have hcore : W.card + (∅ : Finset V).card ≤ workspace := by simpa using hW
  have hbudget : workspace + 0 * lmGrowthRounds (Fintype.card V) ≤
      lmGrowthGain (Fintype.card V) D := by simpa using hworkspace
  simpa using exists_avoiding_path_between_of_lmLimitedContact G d D workspace 0
    hexp A B W ∅ ∅ hN hd hAcard hBcard hcutoff hlarge hcore hbudget
      (by simp) (by simp)
      (by
        intro r
        have hempty : blockedExternalNeighborhood G (((∅ : Finset V) : Set V))
            (ballAvoidingFrom G (((∅ : Finset V) : Set V)) A r) = ∅ := by
          ext z
          simp
        rw [hempty]
        simp)
      (by
        intro r
        have hempty : blockedExternalNeighborhood G (((∅ : Finset V) : Set V))
            (ballAvoidingFrom G (((∅ : Finset V) : Set V)) B r) = ∅ := by
          ext z
          simp
        rw [hempty]
        simp)

/-- Uniform form of the small-deletion connector.  If `D` is below the LM
cutoff, a radius-one minimum-degree neighborhood is used before the concrete
multiplicative schedule.  This is the small-`x` branch of Lemma 3.4 and is
why no comparison between `d` and `D` appears in the statement. -/
theorem exists_avoiding_path_between_of_lmSmallDeletionBootstrap
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d D workspace : ℕ)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (W A B : Finset V)
    (hN : 32 ≤ Fintype.card V) (hd : 1 ≤ d)
    (hAcard : D ≤ A.card) (hBcard : D ≤ B.card)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAW : Disjoint A W) (hBW : Disjoint B W)
    (hlarge : 2 * lmGrowthDivisor (Fintype.card V) ≤ D)
    (hW : W.card ≤ workspace)
    (hworkspace : workspace ≤ lmGrowthGain (Fintype.card V) D) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsAvoidingPath (W : Set V) ({a, b} : Set V) ∧
        p.length ≤ 2 * (lmGrowthRounds (Fintype.card V) + 1) := by
  let start := lmSeedStart d D workspace
  have hworkspaceD : workspace ≤ D :=
    hworkspace.trans (Nat.div_le_self D (lmGrowthDivisor (Fintype.card V)))
  have hDstart : D ≤ start := lmSeedStart_base_le hworkspaceD
  have hcutoff : (d : ℝ) / 128 ≤ (start : ℝ) :=
    lmSeedStart_cutoff hworkspaceD
  have hlargeStart : 2 * lmGrowthDivisor (Fintype.card V) ≤ start :=
    hlarge.trans hDstart
  have hworkspaceStart :
      workspace ≤ lmGrowthGain (Fintype.card V) start :=
    hworkspace.trans (lmGrowthGain_mono _ hDstart)
  have hseed := lmSeedStart_direct_or_bootstrap (d := d) hworkspaceD
  have hAseed : start ≤ A.card ∨ start + workspace ≤ d := by
    rcases hseed with hseed | hseed
    · exact Or.inl (hseed.trans hAcard)
    · exact Or.inr hseed
  have hBseed : start ≤ B.card ∨ start + workspace ≤ d := by
    rcases hseed with hseed | hseed
    · exact Or.inl (hseed.trans hBcard)
    · exact Or.inr hseed
  obtain ⟨a, ha, b, hb, p, hp, hpavoid, hplen⟩ :=
    exists_short_set_connector_ge G (1 / 1024) ((1 / 64) * (d : ℝ))
      hexp d hdegree W A B start workspace
        (lmGrowthRounds (Fintype.card V)) hW hA hB hAseed hBseed hAW hBW
        (concreteBallGrowthSchedule G d start workspace hN hd hcutoff
          hlargeStart hworkspaceStart)
  exact ⟨a, ha, b, hb, p, ⟨hp, hpavoid.mono_permitted (by simp)⟩, hplen⟩

/-! ## The concrete adjuster-join successor -/

/-- A schedule-free successor step for Lemma 4.7.  Both ends are used as the
two growth seeds; the paid deletion contains only the ambient forbidden set
and the two adjuster cores. -/
theorem AdjusterJoin.stepOfConcreteGrowth
    [Fintype V] [DecidableRel G.Adj]
    {D m mB k d workspace : ℕ}
    (A : Adjuster G D m k) (B₀ : Adjuster G D mB 1) (hmB : mB ≤ m)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint forbidden A.verts)
    (hforbiddenB : Disjoint forbidden B₀.verts)
    (hN : 32 ≤ Fintype.card V) (hd : 1 ≤ d)
    (hlarge : 2 * lmGrowthDivisor (Fintype.card V) ≤ 2 * D)
    (hsmall : (adjusterJoinSmallBarrier forbidden A B₀).card ≤ workspace)
    (hworkspace : workspace ≤ lmGrowthGain (Fintype.card V) (2 * D))
    (hcard : A.core.card + B₀.core.card +
        (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1 ≤
          10 * m * (k + 1)) :
    ∃ C : Adjuster G D m (k + 1), Disjoint forbidden C.verts := by
  have hAW : Disjoint (adjusterEnds A)
      (adjusterJoinSmallBarrier forbidden A B₀) := by
    rw [Finset.disjoint_left]
    intro z hzends hzbarrier
    simp only [adjusterEnds, Finset.mem_union] at hzends
    simp only [adjusterJoinSmallBarrier, Finset.mem_union] at hzbarrier
    rcases hzends with hzleft | hzright
    · rcases hzbarrier with (hzforbidden | hzAcore) | hzBcore
      · exact Finset.disjoint_left.1 hforbiddenA hzforbidden
          (A.leftEnd_verts_subset hzleft)
      · exact Finset.disjoint_left.1 A.core_disjoint_left hzAcore hzleft
      · exact Finset.disjoint_left.1 hAB (A.leftEnd_verts_subset hzleft)
          (B₀.core_subset_verts hzBcore)
    · rcases hzbarrier with (hzforbidden | hzAcore) | hzBcore
      · exact Finset.disjoint_left.1 hforbiddenA hzforbidden
          (A.rightEnd_verts_subset hzright)
      · exact Finset.disjoint_left.1 A.core_disjoint_right hzAcore hzright
      · exact Finset.disjoint_left.1 hAB (A.rightEnd_verts_subset hzright)
          (B₀.core_subset_verts hzBcore)
  have hBW : Disjoint (adjusterEnds B₀)
      (adjusterJoinSmallBarrier forbidden A B₀) := by
    rw [Finset.disjoint_left]
    intro z hzends hzbarrier
    simp only [adjusterEnds, Finset.mem_union] at hzends
    simp only [adjusterJoinSmallBarrier, Finset.mem_union] at hzbarrier
    rcases hzends with hzleft | hzright
    · rcases hzbarrier with (hzforbidden | hzAcore) | hzBcore
      · exact Finset.disjoint_left.1 hforbiddenB hzforbidden
          (B₀.leftEnd_verts_subset hzleft)
      · exact Finset.disjoint_left.1 hAB (A.core_subset_verts hzAcore)
          (B₀.leftEnd_verts_subset hzleft)
      · exact Finset.disjoint_left.1 B₀.core_disjoint_left hzBcore hzleft
    · rcases hzbarrier with (hzforbidden | hzAcore) | hzBcore
      · exact Finset.disjoint_left.1 hforbiddenB hzforbidden
          (B₀.rightEnd_verts_subset hzright)
      · exact Finset.disjoint_left.1 hAB (A.core_subset_verts hzAcore)
          (B₀.rightEnd_verts_subset hzright)
      · exact Finset.disjoint_left.1 B₀.core_disjoint_right hzBcore hzright
  obtain ⟨a, ha, b, hb, p, hp, hplen⟩ :=
    exists_avoiding_path_between_of_lmSmallDeletionBootstrap G d (2 * D) workspace
      hexp hdegree (adjusterJoinSmallBarrier forbidden A B₀) (adjusterEnds A)
        (adjusterEnds B₀) hN hd (by simp) (by simp)
        ⟨A.leftRoot, by simp [adjusterEnds, A.leftEnd.root_mem]⟩
        ⟨B₀.leftRoot, by simp [adjusterEnds, B₀.leftEnd.root_mem]⟩
        hAW hBW hlarge hsmall hworkspace
  exact AdjusterJoin.stepOfEndpointUnionRawConnector A B₀ hmB forbidden hAB
    hforbiddenA hforbiddenB ha hb p hp hplen hcard

/-- Source-parameter form of `stepOfConcreteGrowth`.  The caller supplies
only the small paid-workspace estimate; all profile and round-count facts are
read from `LMConcreteGrowthBounds`. -/
theorem AdjusterJoin.stepOfConcreteGrowthOfBounds
    [Fintype V] [DecidableRel G.Adj]
    {m mB k d workspace : ℕ}
    (A : Adjuster G (Parameters.lmExpansionOrder (Fintype.card V)) m k)
    (B₀ : Adjuster G (Parameters.lmExpansionOrder (Fintype.card V)) mB 1)
    (hmB : mB ≤ m)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (bounds : LMConcreteGrowthBounds (Fintype.card V) d)
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint forbidden A.verts)
    (hforbiddenB : Disjoint forbidden B₀.verts)
    (hsmall : (adjusterJoinSmallBarrier forbidden A B₀).card ≤ workspace)
    (hworkspace : workspace ≤
      500 * Parameters.lmRadius (1 / 1024) (Fintype.card V) ^ 2)
    (hcard : A.core.card + B₀.core.card +
        (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1 ≤
          10 * m * (k + 1)) :
    ∃ C : Adjuster G (Parameters.lmExpansionOrder (Fintype.card V)) m (k + 1),
      Disjoint forbidden C.verts := by
  apply AdjusterJoin.stepOfConcreteGrowth A B₀ hmB hexp hdegree forbidden hAB
    hforbiddenA hforbiddenB bounds.card_large bounds.degree_pos
    bounds.endpoint_large hsmall
    (hworkspace.trans bounds.workspace_absorbed) hcard

/-- Generic direct-or-bootstrap Lemma 4.7 induction.  Unlike the
source-parameter specialization below, the end order and the paid workspace
are explicit.  This is the form used at the inflated order `M = Dm`. -/
theorem AdjusterJoin.lemma4_7_of_simple_supply_and_concreteBootstrap
    [Fintype V] [DecidableRel G.Adj]
    {D m mB d : ℕ}
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (forbidden : Finset V) (r simpleBudget workspace : ℕ)
    (hN : 32 ≤ Fintype.card V) (hd : 1 ≤ d) (hrpos : 0 < r)
    (hsupply : ∀ U : Finset V, U.card ≤ simpleBudget →
      ∃ B : Adjuster G D mB 1, Disjoint U B.verts)
    (hmB : mB ≤ m)
    (hlarge : 2 * lmGrowthDivisor (Fintype.card V) ≤ 2 * D)
    (hsupplyCap : forbidden.card + 2 * D + 10 * m * r ≤ simpleBudget)
    (hworkspaceCap : forbidden.card + 10 * m * r + 10 * mB ≤ workspace)
    (hworkspace : workspace ≤ lmGrowthGain (Fintype.card V) (2 * D))
    (hjoinCapacity :
      10 * mB +
          (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1 ≤ 10 * m) :
    ∃ A : Adjuster G D m r, Disjoint forbidden A.verts := by
  induction r with
  | zero => omega
  | succ j ih =>
      by_cases hj : j = 0
      · subst j
        have hforbiddenBudget : forbidden.card ≤ simpleBudget := by omega
        obtain ⟨B₀, hB⟩ := hsupply forbidden hforbiddenBudget
        exact ⟨B₀.widenRadius hmB, by simpa using hB⟩
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
        have hsupplyCapJ : forbidden.card + 2 * D + 10 * m * j ≤
            simpleBudget := by
          apply hsupplyCap.trans'
          gcongr
          omega
        have hworkspaceCapJ : forbidden.card + 10 * m * j + 10 * mB ≤
            workspace := by
          apply hworkspaceCap.trans'
          gcongr
          omega
        obtain ⟨A, hforbiddenA⟩ := ih hjpos hsupplyCapJ hworkspaceCapJ
        let U := forbidden ∪ A.verts
        have hUcard : U.card ≤ simpleBudget := by
          calc
            U.card ≤ forbidden.card + A.verts.card := Finset.card_union_le _ _
            _ ≤ forbidden.card + (2 * D + 10 * m * j) :=
              Nat.add_le_add_left A.card_verts_le _
            _ ≤ simpleBudget := by simpa [Nat.add_assoc] using hsupplyCapJ
        obtain ⟨B₀, hUB⟩ := hsupply U hUcard
        have hAB : Disjoint A.verts B₀.verts := by
          rw [Finset.disjoint_left]
          intro z hzA hzB
          exact Finset.disjoint_left.1 hUB (by simp [U, hzA]) hzB
        have hforbiddenB : Disjoint forbidden B₀.verts := by
          rw [Finset.disjoint_left]
          intro z hzforbidden hzB
          exact Finset.disjoint_left.1 hUB (by simp [U, hzforbidden]) hzB
        have hsmall :
            (adjusterJoinSmallBarrier forbidden A B₀).card ≤ workspace := by
          have hAcore := A.core_card_le
          have hBcore := B₀.core_card_le
          have h₁ := Finset.card_union_le forbidden A.core
          have h₂ := Finset.card_union_le (forbidden ∪ A.core) B₀.core
          dsimp [adjusterJoinSmallBarrier]
          omega
        have hcard : A.core.card + B₀.core.card +
            (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1 ≤
              10 * m * (j + 1) := by
          have hrest : B₀.core.card +
              (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1 ≤
                10 * m := by
            have hBcore' : B₀.core.card ≤ 10 * mB := by
              simpa using B₀.core_card_le
            calc
              B₀.core.card +
                    (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1
                  ≤ 10 * mB +
                    (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1 := by
                      omega
              _ ≤ 10 * m := hjoinCapacity
          calc
            A.core.card + B₀.core.card +
                  (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1
                = A.core.card + (B₀.core.card +
                  (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1) := by
                    omega
            _ ≤ 10 * m * j + 10 * m := Nat.add_le_add A.core_card_le hrest
            _ = 10 * m * (j + 1) := by rw [Nat.mul_add]; simp
        exact AdjusterJoin.stepOfConcreteGrowth A B₀ hmB hexp hdegree forbidden hAB
          hforbiddenA hforbiddenB hN hd hlarge hsmall hworkspace hcard

/-- Full schedule-free Lemma 4.7 induction.  The only supplied graph gadget
is the robust simple-adjuster conclusion of Lemma 4.3; every successor join
uses the concrete LM profile above. -/
theorem AdjusterJoin.lemma4_7_of_simple_supply_and_concreteGrowth
    [Fintype V] [DecidableRel G.Adj]
    {m mB d : ℕ}
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (bounds : LMConcreteGrowthBounds (Fintype.card V) d)
    (forbidden : Finset V) (r simpleBudget workspace : ℕ)
    (hrpos : 0 < r)
    (hsupply : ∀ U : Finset V, U.card ≤ simpleBudget →
      ∃ B : Adjuster G (Parameters.lmExpansionOrder (Fintype.card V)) mB 1,
        Disjoint U B.verts)
    (hmB : mB ≤ m)
    (hsupplyCap : forbidden.card +
      2 * Parameters.lmExpansionOrder (Fintype.card V) + 10 * m * r ≤
        simpleBudget)
    (hworkspaceCap : forbidden.card + 10 * m * r + 10 * mB ≤ workspace)
    (hworkspace : workspace ≤
      500 * Parameters.lmRadius (1 / 1024) (Fintype.card V) ^ 2)
    (hjoinCapacity :
      10 * mB +
          (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1 ≤ 10 * m) :
    ∃ A : Adjuster G (Parameters.lmExpansionOrder (Fintype.card V)) m r,
      Disjoint forbidden A.verts := by
  let D := Parameters.lmExpansionOrder (Fintype.card V)
  induction r with
  | zero => omega
  | succ j ih =>
      by_cases hj : j = 0
      · subst j
        have hforbiddenBudget : forbidden.card ≤ simpleBudget := by omega
        obtain ⟨B₀, hB⟩ := hsupply forbidden hforbiddenBudget
        exact ⟨B₀.widenRadius hmB, by simpa using hB⟩
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
        have hsupplyCapJ : forbidden.card + 2 * D + 10 * m * j ≤
            simpleBudget := by
          apply hsupplyCap.trans'
          dsimp [D]
          gcongr
          omega
        have hworkspaceCapJ : forbidden.card + 10 * m * j + 10 * mB ≤
            workspace := by
          apply hworkspaceCap.trans'
          gcongr
          omega
        obtain ⟨A, hforbiddenA⟩ := ih hjpos hsupplyCapJ hworkspaceCapJ
        let U := forbidden ∪ A.verts
        have hUcard : U.card ≤ simpleBudget := by
          calc
            U.card ≤ forbidden.card + A.verts.card := Finset.card_union_le _ _
            _ ≤ forbidden.card + (2 * D + 10 * m * j) :=
              Nat.add_le_add_left A.card_verts_le _
            _ ≤ simpleBudget := by simpa [Nat.add_assoc] using hsupplyCapJ
        obtain ⟨B₀, hUB⟩ := hsupply U hUcard
        have hAB : Disjoint A.verts B₀.verts := by
          rw [Finset.disjoint_left]
          intro z hzA hzB
          exact Finset.disjoint_left.1 hUB (by simp [U, hzA]) hzB
        have hforbiddenB : Disjoint forbidden B₀.verts := by
          rw [Finset.disjoint_left]
          intro z hzforbidden hzB
          exact Finset.disjoint_left.1 hUB (by simp [U, hzforbidden]) hzB
        have hsmall :
            (adjusterJoinSmallBarrier forbidden A B₀).card ≤ workspace := by
          have hAcore := A.core_card_le
          have hBcore := B₀.core_card_le
          have h₁ := Finset.card_union_le forbidden A.core
          have h₂ := Finset.card_union_le (forbidden ∪ A.core) B₀.core
          dsimp [adjusterJoinSmallBarrier]
          omega
        have hcard : A.core.card + B₀.core.card +
            (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1 ≤
              10 * m * (j + 1) := by
          have hrest : B₀.core.card +
              (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1 ≤
                10 * m := by
            have hBcore' : B₀.core.card ≤ 10 * mB := by
              simpa using B₀.core_card_le
            calc
              B₀.core.card +
                    (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1
                  ≤ 10 * mB +
                    (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1 := by
                      omega
              _ ≤ 10 * m := hjoinCapacity
          calc
            A.core.card + B₀.core.card +
                  (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1
                = A.core.card + (B₀.core.card +
                  (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1) := by
                    omega
            _ ≤ 10 * m * j + 10 * m := Nat.add_le_add A.core_card_le hrest
            _ = 10 * m * (j + 1) := by rw [Nat.mul_add]; simp
        exact AdjusterJoin.stepOfConcreteGrowthOfBounds A B₀ hmB hexp hdegree bounds
          forbidden hAB hforbiddenA hforbiddenB hsmall hworkspace hcard

/-- The exact range needed by Lemma 4.8. -/
theorem AdjusterJoin.lemma4_7_twentyTwo_of_concreteGrowth
    [Fintype V] [DecidableRel G.Adj]
    {m mB d simpleBudget workspace : ℕ} (hmpos : 0 < m)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (bounds : LMConcreteGrowthBounds (Fintype.card V) d)
    (forbidden : Finset V)
    (hsupply : ∀ U : Finset V, U.card ≤ simpleBudget →
      ∃ B : Adjuster G (Parameters.lmExpansionOrder (Fintype.card V)) mB 1,
        Disjoint U B.verts)
    (hmB : mB ≤ m)
    (hsupplyCap : forbidden.card +
      2 * Parameters.lmExpansionOrder (Fintype.card V) + 10 * m * (22 * m) ≤
        simpleBudget)
    (hworkspaceCap :
      forbidden.card + 10 * m * (22 * m) + 10 * mB ≤ workspace)
    (hworkspace : workspace ≤
      500 * Parameters.lmRadius (1 / 1024) (Fintype.card V) ^ 2)
    (hjoinCapacity :
      10 * mB +
          (m + 2 * (lmGrowthRounds (Fintype.card V) + 1) + mB) + 1 ≤ 10 * m) :
    ∃ A : Adjuster G (Parameters.lmExpansionOrder (Fintype.card V)) m (22 * m),
      Disjoint forbidden A.verts := by
  exact AdjusterJoin.lemma4_7_of_simple_supply_and_concreteGrowth hexp hdegree bounds
    forbidden (22 * m) simpleBudget workspace (by positivity) hsupply hmB
      hsupplyCap hworkspaceCap hworkspace hjoinCapacity

/-- Corrected source-feasible Lemma 4.7 wrapper.  The whole induction runs
at end order `M = Dm`; hence the two already constructed `D`-expansions may
be included in `protected` and paid for by the ordinary LM connector. -/
theorem AdjusterJoin.lemma4_7_twentyTwo_inflated_of_concreteGrowth
    [Fintype V] [DecidableRel G.Adj]
    {d : ℕ}
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (bounds : LMConcreteGrowthBounds (Fintype.card V) d)
    (scales : LM47ScaleBounds (Fintype.card V))
    (protectedSet : Finset V)
    (hprotected : protectedSet.card ≤
      2 * Parameters.lmExpansionOrder (Fintype.card V))
    (hsupply : ∀ U : Finset V,
      U.card ≤ lm47SimpleBudget (Fintype.card V) →
      ∃ B : Adjuster G (lm47InflatedOrder (Fintype.card V))
          (2 * Parameters.lmSimpleRadius (1 / 1024) (Fintype.card V)) 1,
        Disjoint U B.verts) :
    ∃ A : Adjuster G (lm47InflatedOrder (Fintype.card V))
        (Parameters.lmRadius (1 / 1024) (Fintype.card V))
        (22 * Parameters.lmRadius (1 / 1024) (Fintype.card V)),
      Disjoint protectedSet A.verts := by
  let n := Fintype.card V
  let D := Parameters.lmExpansionOrder n
  let m := Parameters.lmRadius (1 / 1024) n
  let mB := 2 * Parameters.lmSimpleRadius (1 / 1024) n
  let M := lm47InflatedOrder n
  let simpleBudget := lm47SimpleBudget n
  let workspace := lm47Workspace n
  have hmpos : 0 < m := by
    have hconnector := bounds.connector_radius
    change 2 * (lmGrowthRounds n + 1) ≤ m at hconnector
    omega
  have hmB : mB ≤ m := by
    simpa [mB, m, n] using scales.simple_radius_le
  have hlarge : 2 * lmGrowthDivisor n ≤ 2 * M := by
    simpa [M, n] using scales.inflated_endpoint_large
  have hsupplyScale : 2 * D + 2 * M + 220 * m ^ 2 ≤ simpleBudget := by
    simpa [D, M, m, simpleBudget, n] using scales.supply_capacity
  have hsupplyCap : protectedSet.card + 2 * M + 10 * m * (22 * m) ≤
      simpleBudget := by
    have hp : protectedSet.card ≤ 2 * D := by simpa [D, n] using hprotected
    rw [show 10 * m * (22 * m) = 220 * m ^ 2 by ring]
    have hcap : protectedSet.card + 2 * M + 220 * m ^ 2 ≤
        2 * D + 2 * M + 220 * m ^ 2 := by omega
    exact hcap.trans hsupplyScale
  have hworkspaceScale : 2 * D + 220 * m ^ 2 + 10 * mB ≤ workspace := by
    simpa [D, m, mB, workspace, n] using scales.workspace_capacity
  have hworkspaceCap : protectedSet.card + 10 * m * (22 * m) + 10 * mB ≤
      workspace := by
    have hp : protectedSet.card ≤ 2 * D := by simpa [D, n] using hprotected
    rw [show 10 * m * (22 * m) = 220 * m ^ 2 by ring]
    have hcap : protectedSet.card + 220 * m ^ 2 + 10 * mB ≤
        2 * D + 220 * m ^ 2 + 10 * mB := by omega
    exact hcap.trans hworkspaceScale
  have hworkspace : workspace ≤ lmGrowthGain n (2 * M) := by
    simpa [workspace, M, n] using scales.inflated_workspace_absorbed
  have hjoin :
      10 * mB + (m + 2 * (lmGrowthRounds n + 1) + mB) + 1 ≤ 10 * m := by
    simpa [mB, m, n] using scales.join_capacity
  simpa [n, m, M] using
    (AdjusterJoin.lemma4_7_of_simple_supply_and_concreteBootstrap
      (D := M) (m := m) (mB := mB) hexp hdegree protectedSet
      (22 * m) simpleBudget workspace bounds.card_large bounds.degree_pos
      (by positivity) (by simpa [n, M, mB, simpleBudget] using hsupply)
      hmB hlarge hsupplyCap hworkspaceCap hworkspace hjoin)

/-- Final bookkeeping form of the corrected Lemma 4.7 wrapper: after the
inflated-order joins, Proposition 3.10 shrinks both surviving ends back to
order `D`, without changing the core or losing avoidance. -/
theorem AdjusterJoin.lemma4_7_twentyTwo_shrunk_of_concreteGrowth
    [Fintype V] [DecidableRel G.Adj]
    {d : ℕ}
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (bounds : LMConcreteGrowthBounds (Fintype.card V) d)
    (scales : LM47ScaleBounds (Fintype.card V))
    (protectedSet : Finset V)
    (hprotected : protectedSet.card ≤
      2 * Parameters.lmExpansionOrder (Fintype.card V))
    (hsupply : ∀ U : Finset V,
      U.card ≤ lm47SimpleBudget (Fintype.card V) →
      ∃ B : Adjuster G (lm47InflatedOrder (Fintype.card V))
          (2 * Parameters.lmSimpleRadius (1 / 1024) (Fintype.card V)) 1,
        Disjoint U B.verts) :
    ∃ A : Adjuster G (Parameters.lmExpansionOrder (Fintype.card V))
        (Parameters.lmRadius (1 / 1024) (Fintype.card V))
        (22 * Parameters.lmRadius (1 / 1024) (Fintype.card V)),
      Disjoint protectedSet A.verts := by
  obtain ⟨A, hA⟩ :=
    AdjusterJoin.lemma4_7_twentyTwo_inflated_of_concreteGrowth
      hexp hdegree bounds scales protectedSet hprotected hsupply
  obtain ⟨A', _, _, _, hsubset⟩ :=
    A.exists_shrinkEnds_subset scales.endpoint_pos scales.shrink_le
  exact ⟨A', hA.mono_right hsubset⟩

/-- The protected-set successor step used in Lemma 4.8.  `protected` may be
large: it is not included in the globally paid workspace and is charged only
through the two limited-contact hypotheses.  The output nevertheless avoids
both `forbiddenSmall` and `protected`. -/
theorem AdjusterJoin.stepOfConcreteLimitedContactGrowth
    [Fintype V] [DecidableRel G.Adj]
    {D m mB k d core contact : ℕ}
    (A : Adjuster G D m k) (B₀ : Adjuster G D mB 1) (hmB : mB ≤ m)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (forbiddenSmall protectedSet : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint (forbiddenSmall ∪ protectedSet) A.verts)
    (hforbiddenB : Disjoint (forbiddenSmall ∪ protectedSet) B₀.verts)
    (hN : 32 ≤ Fintype.card V) (hd : 1 ≤ d)
    (hcutoff : (d : ℝ) / 128 ≤ ((2 * D : ℕ) : ℝ))
    (hlarge : 2 * lmGrowthDivisor (Fintype.card V) ≤ 2 * D)
    (hsmall : (adjusterJoinSmallBarrier forbiddenSmall A B₀).card ≤ core)
    (hcontactBudget :
      core + contact * lmGrowthRounds (Fintype.card V) ≤
        lmGrowthGain (Fintype.card V) (2 * D))
    (hcontactA : HasLimitedContact G (adjusterEnds A) (protectedSet : Set V) contact)
    (hcontactB : HasLimitedContact G (adjusterEnds B₀) (protectedSet : Set V) contact)
    (hcard : A.core.card + B₀.core.card +
        (m + 2 * lmGrowthRounds (Fintype.card V) + mB) + 1 ≤
          10 * m * (k + 1)) :
    ∃ C : Adjuster G D m (k + 1),
      Disjoint (forbiddenSmall ∪ protectedSet) C.verts := by
  have hendsA : adjusterEnds A ⊆ A.verts := by
    intro z hz
    simp only [adjusterEnds, Finset.mem_union] at hz
    rcases hz with hz | hz
    · exact A.leftEnd_verts_subset hz
    · exact A.rightEnd_verts_subset hz
  have hendsB : adjusterEnds B₀ ⊆ B₀.verts := by
    intro z hz
    simp only [adjusterEnds, Finset.mem_union] at hz
    rcases hz with hz | hz
    · exact B₀.leftEnd_verts_subset hz
    · exact B₀.rightEnd_verts_subset hz
  have hAZ : ∀ z ∈ adjusterEnds A, z ∉ protectedSet := by
    intro z hz hzP
    exact Finset.disjoint_left.1 hforbiddenA (by simp [hzP]) (hendsA hz)
  have hBZ : ∀ z ∈ adjusterEnds B₀, z ∉ protectedSet := by
    intro z hz hzP
    exact Finset.disjoint_left.1 hforbiddenB (by simp [hzP]) (hendsB hz)
  have hcore : (adjusterJoinSmallBarrier forbiddenSmall A B₀).card +
      (∅ : Finset V).card ≤ core := by simpa using hsmall
  obtain ⟨a, ha, b, hb, p, hp, hplen⟩ :=
    exists_avoiding_path_between_of_lmLimitedContact G d (2 * D) core contact
      hexp (adjusterEnds A) (adjusterEnds B₀)
        (adjusterJoinSmallBarrier forbiddenSmall A B₀) ∅ protectedSet
        hN hd (by simp) (by simp) hcutoff hlarge hcore hcontactBudget
          hAZ hBZ hcontactA hcontactB
  have hforbiddenSubset :
      (adjusterJoinSmallBarrier (forbiddenSmall ∪ protectedSet) A B₀ : Set V) ⊆
        (adjusterJoinSmallBarrier forbiddenSmall A B₀ : Set V) ∪
          ((∅ : Finset V) : Set V) ∪ (protectedSet : Set V) := by
    intro z hz
    simp only [adjusterJoinSmallBarrier, Finset.coe_union, Set.mem_union,
      Set.mem_empty_iff_false, or_false] at hz ⊢
    tauto
  have hp' : p.IsAvoidingPath
      (adjusterJoinSmallBarrier (forbiddenSmall ∪ protectedSet) A B₀ : Set V)
      ({a, b} : Set V) := hp.mono_forbidden hforbiddenSubset
  exact AdjusterJoin.stepOfEndpointUnionRawConnector A B₀ hmB
    (forbiddenSmall ∪ protectedSet) hAB hforbiddenA hforbiddenB
      ha hb p hp' hplen hcard

end Erdos63
