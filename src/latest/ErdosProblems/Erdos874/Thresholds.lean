/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.Foundations

/-!
# Numerical thresholds for the Deshouillers--Freiman argument

The papers use several estimates only for sufficiently large `N`.  This file
records the elementary analytic facts which allow all of those occurrences of
`O(N^α)` to be replaced by ordinary `∀ᶠ N in atTop` inequalities.  The main
lemma says that a fixed multiple of a smaller real power is eventually bounded
by a larger real power.  The named specializations are the exponents occurring
in the 1995 and 1999 papers.

This file also defines the two integral scales used in the finite block
decomposition.  Floors are part of the definitions, so later combinatorial
files do not need to make an implicit rounding convention.
-/

open Filter
open scoped Topology

namespace Erdos874

noncomputable section

/-- Every fixed nonnegative multiple of `N^a` is eventually at most `N^b`
when `a < b`. -/
theorem eventually_const_mul_rpow_le_rpow
    {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  have hdelta : 0 < b - a := sub_pos.mpr hab
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop, C ≤ (N : ℝ) ^ (b - a) :=
    tendsto_atTop.mp hpow C
  filter_upwards [hlarge, eventually_ge_atTop 1] with N hNlarge hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hpow_nonneg : 0 ≤ (N : ℝ) ^ a := Real.rpow_nonneg (by positivity) _
  calc
    C * (N : ℝ) ^ a ≤ (N : ℝ) ^ (b - a) * (N : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hNlarge hpow_nonneg
    _ = (N : ℝ) ^ b := by
      rw [← Real.rpow_add hNpos]
      congr 2
      ring

/-- Strict form of `eventually_const_mul_rpow_le_rpow`. -/
theorem eventually_const_mul_rpow_lt_rpow
    {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ a < (N : ℝ) ^ b := by
  have hdelta : 0 < b - a := sub_pos.mpr hab
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop, C < (N : ℝ) ^ (b - a) :=
    (tendsto_atTop.mp hpow (C + 1)).mono fun _ h => by linarith
  filter_upwards [hlarge, eventually_ge_atTop 1] with N hNlarge hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hpow_pos : 0 < (N : ℝ) ^ a := Real.rpow_pos_of_pos hNpos _
  calc
    C * (N : ℝ) ^ a < (N : ℝ) ^ (b - a) * (N : ℝ) ^ a :=
      mul_lt_mul_of_pos_right hNlarge hpow_pos
    _ = (N : ℝ) ^ b := by
      rw [← Real.rpow_add hNpos]
      congr 2
      ring

/-- The error exponent `5/12` is smaller than the square-root scale. -/
theorem eventually_const_mul_rpow_five_twelfths_le_sqrt (C : ℝ)
    (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ ((5 : ℝ) / 12) ≤ Real.sqrt N := by
  simpa only [Real.sqrt_eq_rpow] using
    (eventually_const_mul_rpow_le_rpow
      (C := C) (a := (5 : ℝ) / 12) (b := (1 : ℝ) / 2) (by norm_num) hC)

/-- The `5/12` error is itself absorbed by the `11/24` central window. -/
theorem eventually_const_mul_rpow_five_twelfths_le_eleven_twentyfourths
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ ((5 : ℝ) / 12) ≤
        (N : ℝ) ^ ((11 : ℝ) / 24) := by
  exact eventually_const_mul_rpow_le_rpow (C := C) (by norm_num) hC

/-- The `11/24` central window is `o(√N)`. -/
theorem eventually_const_mul_rpow_eleven_twentyfourths_le_sqrt
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ ((11 : ℝ) / 24) ≤ Real.sqrt N := by
  simpa only [Real.sqrt_eq_rpow] using
    (eventually_const_mul_rpow_le_rpow
      (C := C) (a := (11 : ℝ) / 24) (b := (1 : ℝ) / 2) (by norm_num) hC)

/-- The short-progression exponent is smaller than the long-progression
exponent. -/
theorem eventually_const_mul_rpow_seven_twelfths_le_five_sixths
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ ((7 : ℝ) / 12) ≤
        (N : ℝ) ^ ((5 : ℝ) / 6) := by
  exact eventually_const_mul_rpow_le_rpow (C := C) (by norm_num) hC

/-- The long-progression exponent is sublinear. -/
theorem eventually_const_mul_rpow_five_sixths_le_id
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ ((5 : ℝ) / 6) ≤ (N : ℝ) := by
  have h := eventually_const_mul_rpow_le_rpow
    (C := C) (a := (5 : ℝ) / 6) (b := (1 : ℝ)) (by norm_num) hC
  filter_upwards [h, eventually_ge_atTop 1] with N hN hNpos
  simpa [Real.rpow_one] using hN

/-- Finite algebra behind the DF99 structural-step estimate.  Once `k` is at
least half the square-root scale, the quadratic endpoint inequality and the
near-extremal cardinality lower bound force both `q` and the deficit
`√N-k` into the same explicit error scale. -/
theorem central_q_k_error
    {N k q : ℕ} {E : ℝ} (hE : 0 ≤ E)
    (hkhalf : Real.sqrt N / 2 ≤ (k : ℝ))
    (hnear : 2 * Real.sqrt N - E ≤ 2 * (k : ℝ) + q)
    (hquad : (k : ℝ) ^ 2 + 2 * (k : ℝ) * q < N) :
    (q : ℝ) < 3 * E ∧ Real.sqrt N - (k : ℝ) < 2 * E := by
  have hNpos : (0 : ℝ) < N := by
    have hleft : 0 ≤ (k : ℝ) ^ 2 + 2 * (k : ℝ) * q := by positivity
    linarith
  have hsqrtPos : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsqrtSq : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
  have hklt : (k : ℝ) < Real.sqrt N := by
    nlinarith [sq_nonneg (Real.sqrt N - k)]
  have hkpos : (0 : ℝ) < k := by linarith
  let δ : ℝ := Real.sqrt N - k
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hprod : 2 * (k : ℝ) * q < δ * (Real.sqrt N + k) := by
    dsimp [δ]
    nlinarith
  have hsum : Real.sqrt N + (k : ℝ) ≤ 3 * k := by linarith
  have hprod' : 2 * (k : ℝ) * q < δ * (3 * k) :=
    hprod.trans_le (mul_le_mul_of_nonneg_left hsum hδ.le)
  have hkineq : (k : ℝ) * (2 * q) < (k : ℝ) * (3 * δ) := by
    nlinarith
  have hqδ : (2 : ℝ) * q < 3 * δ := by
    by_contra hn
    have hge : 3 * δ ≤ (2 : ℝ) * q := le_of_not_gt hn
    have hmulge := mul_le_mul_of_nonneg_left hge hkpos.le
    exact (not_lt_of_ge hmulge) hkineq
  have hnear' : 2 * δ ≤ (q : ℝ) + E := by
    dsimp [δ]
    linarith
  constructor <;> nlinarith

/-- Exact exponent cancellation used in the refined central-span estimate. -/
theorem sqrt_mul_five_twelfths_div_eleven_twentyfourths
    {N : ℕ} (hN : 0 < N) :
    Real.sqrt N * (N : ℝ) ^ ((5 : ℝ) / 12) /
        (N : ℝ) ^ ((11 : ℝ) / 24) =
      (N : ℝ) ^ ((11 : ℝ) / 24) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity),
    ← Real.rpow_sub (by positivity)]
  congr 2
  norm_num

/-- Twice the rounded `10^4 N^(5/12)` scale used for the DF95 blocks. -/
def dfBlockSize (N : ℕ) : ℕ :=
  2 * Nat.floor (10 ^ (4 : ℕ) * (N : ℝ) ^ ((5 : ℝ) / 12))

/-- Rounded `N^(1/6)` residue scale used to repeat the extracted
progression. -/
def dfResidueScale (N : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 6))

/-- Rounded `3 N^(5/12)` central truncation scale in the DF99 refinement. -/
def dfCentralScale (N : ℕ) : ℕ :=
  Nat.floor (3 * (N : ℝ) ^ ((5 : ℝ) / 12))

/-- Rounded `N^(7/12)` length bound for the short structural progression. -/
def dfShortScale (N : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) ^ ((7 : ℝ) / 12))

/-- Rounded `N^(1/4)` scale used to align the residue generators. -/
def dfAlignmentScale (N : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) ^ ((1 : ℝ) / 4))

/-- Canonical integral target for the long progression after modular
alignment.  The ceiling makes the published lower bound literal after
casting back to `ℝ`. -/
def dfLongTarget (N : ℕ) : ℕ :=
  Nat.ceil (3 * (N : ℝ) ^ ((5 : ℝ) / 6))

/-- The canonical long target is at least the required real length. -/
theorem dfLongTarget_cast_ge (N : ℕ) :
    3 * (N : ℝ) ^ ((5 : ℝ) / 6) ≤ (dfLongTarget N : ℝ) := by
  exact Nat.le_ceil _

/-- The ceiling in the canonical long target costs strictly less than one. -/
theorem dfLongTarget_cast_lt_add_one (N : ℕ) :
    (dfLongTarget N : ℝ) <
      3 * (N : ℝ) ^ ((5 : ℝ) / 6) + 1 := by
  exact Nat.ceil_lt_add_one (by positivity)

/-- The block size tends to infinity, so it eventually exceeds any fixed
engine threshold. -/
theorem eventually_le_dfBlockSize (n₁ : ℕ) :
    ∀ᶠ N : ℕ in atTop, n₁ ≤ dfBlockSize N := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ ((5 : ℝ) / 12)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hmul : Tendsto
      (fun N : ℕ => 10 ^ (4 : ℕ) * (N : ℝ) ^ ((5 : ℝ) / 12)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) hp
  have hfloor : Tendsto
      (fun N : ℕ => Nat.floor
        (10 ^ (4 : ℕ) * (N : ℝ) ^ ((5 : ℝ) / 12))) atTop atTop :=
    tendsto_nat_floor_atTop.comp hmul
  have hev := tendsto_atTop.mp hfloor n₁
  filter_upwards [hev] with N hN
  dsimp [dfBlockSize]
  omega

/-- The residue scale is eventually positive. -/
theorem eventually_one_le_dfResidueScale :
    ∀ᶠ N : ℕ in atTop, 1 ≤ dfResidueScale N := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hfloor : Tendsto dfResidueScale atTop atTop :=
    tendsto_nat_floor_atTop.comp hp
  exact tendsto_atTop.mp hfloor 1

/-- The central truncation scale is eventually positive. -/
theorem eventually_one_le_dfCentralScale :
    ∀ᶠ N : ℕ in atTop, 1 ≤ dfCentralScale N := by
  have hp : Tendsto (fun N : ℕ => 3 * (N : ℝ) ^ ((5 : ℝ) / 12)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num)
      ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
  exact tendsto_atTop.mp (tendsto_nat_floor_atTop.comp hp) 1

/-- The floor in `dfBlockSize` gives the expected uniform upper bound. -/
theorem dfBlockSize_cast_le (N : ℕ) :
    (dfBlockSize N : ℝ) ≤
      20000 * (N : ℝ) ^ ((5 : ℝ) / 12) := by
  have hfloor := Nat.floor_le
    (show 0 ≤ 10 ^ (4 : ℕ) * (N : ℝ) ^ ((5 : ℝ) / 12) by positivity)
  dsimp [dfBlockSize]
  push_cast
  norm_num at hfloor ⊢
  linarith

/-- Away from `N=0`, rounding loses less than five percent of the DF95
block scale. -/
theorem dfBlockSize_cast_ge {N : ℕ} (hN : 1 ≤ N) :
    19000 * (N : ℝ) ^ ((5 : ℝ) / 12) ≤
      (dfBlockSize N : ℝ) := by
  let p : ℝ := (N : ℝ) ^ ((5 : ℝ) / 12)
  have hp : 1 ≤ p :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hfloor := Nat.lt_floor_add_one (10 ^ (4 : ℕ) * p)
  dsimp [dfBlockSize, p] at hfloor ⊢
  push_cast at hfloor ⊢
  norm_num at hfloor ⊢
  linarith

/-- The residue floor never exceeds its underlying real power. -/
theorem dfResidueScale_cast_le (N : ℕ) :
    (dfResidueScale N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 6) := by
  exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)

/-- Upper floor bound for the DF99 central truncation scale. -/
theorem dfCentralScale_cast_le (N : ℕ) :
    (dfCentralScale N : ℝ) ≤
      3 * (N : ℝ) ^ ((5 : ℝ) / 12) := by
  exact Nat.floor_le (by positivity)

/-- Upper floor bound for the short structural progression length. -/
theorem dfShortScale_cast_le (N : ℕ) :
    (dfShortScale N : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 12) := by
  exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)

/-- Upper floor bound for the alignment scale. -/
theorem dfAlignmentScale_cast_le (N : ℕ) :
    (dfAlignmentScale N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
  exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)

/-- The residue floor is eventually at least nine tenths of its real
power. -/
theorem eventually_dfResidueScale_cast_ge :
    ∀ᶠ N : ℕ in atTop,
      (9 : ℝ) / 10 * (N : ℝ) ^ ((1 : ℝ) / 6) ≤
        (dfResidueScale N : ℝ) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop,
      10 ≤ (N : ℝ) ^ ((1 : ℝ) / 6) := tendsto_atTop.mp hp 10
  filter_upwards [hlarge] with N hN
  have hfloor := Nat.lt_floor_add_one ((N : ℝ) ^ ((1 : ℝ) / 6))
  dsimp [dfResidueScale]
  push_cast at hfloor
  linarith

/-- The central truncation floor is eventually at least `2.9 N^(5/12)`. -/
theorem eventually_dfCentralScale_cast_ge :
    ∀ᶠ N : ℕ in atTop,
      (29 : ℝ) / 10 * (N : ℝ) ^ ((5 : ℝ) / 12) ≤
        (dfCentralScale N : ℝ) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ ((5 : ℝ) / 12)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop,
      10 ≤ (N : ℝ) ^ ((5 : ℝ) / 12) := tendsto_atTop.mp hp 10
  filter_upwards [hlarge] with N hN
  have hfloor := Nat.lt_floor_add_one
    (3 * (N : ℝ) ^ ((5 : ℝ) / 12))
  dsimp [dfCentralScale]
  nlinarith

/-- The short-progression floor is eventually at least ninety percent of its
real scale. -/
theorem eventually_dfShortScale_cast_ge :
    ∀ᶠ N : ℕ in atTop,
      (9 : ℝ) / 10 * (N : ℝ) ^ ((7 : ℝ) / 12) ≤
        (dfShortScale N : ℝ) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ ((7 : ℝ) / 12)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop,
      10 ≤ (N : ℝ) ^ ((7 : ℝ) / 12) := tendsto_atTop.mp hp 10
  filter_upwards [hlarge] with N hN
  have hfloor := Nat.lt_floor_add_one ((N : ℝ) ^ ((7 : ℝ) / 12))
  dsimp [dfShortScale]
  nlinarith

/-- The alignment floor is eventually at least ninety percent of its real
scale. -/
theorem eventually_dfAlignmentScale_cast_ge :
    ∀ᶠ N : ℕ in atTop,
      (9 : ℝ) / 10 * (N : ℝ) ^ ((1 : ℝ) / 4) ≤
        (dfAlignmentScale N : ℝ) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop,
      10 ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := tendsto_atTop.mp hp 10
  filter_upwards [hlarge] with N hN
  have hfloor := Nat.lt_floor_add_one ((N : ℝ) ^ ((1 : ℝ) / 4))
  dsimp [dfAlignmentScale]
  nlinarith

private lemma rpow_five_twelfths_mul_self {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ ((5 : ℝ) / 12) * (N : ℝ) ^ ((5 : ℝ) / 12) =
      (N : ℝ) ^ ((5 : ℝ) / 6) := by
  rw [← Real.rpow_add (by positivity)]
  congr 2
  norm_num

private lemma rpow_one_sixth_mul_five_sixths {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ ((1 : ℝ) / 6) * (N : ℝ) ^ ((5 : ℝ) / 6) = N := by
  rw [← Real.rpow_add (by positivity)]
  norm_num

private lemma rpow_one_sixth_sq {N : ℕ} (hN : 0 < N) :
    ((N : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 =
      (N : ℝ) ^ ((1 : ℝ) / 3) := by
  rw [pow_two, ← Real.rpow_add (by positivity)]
  congr 2
  norm_num

private lemma rpow_one_sixth_cube {N : ℕ} (hN : 0 < N) :
    ((N : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 = Real.sqrt N := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_one,
    rpow_one_sixth_sq hN, Real.sqrt_eq_rpow,
    ← Real.rpow_add (by positivity)]
  congr 2
  norm_num

private lemma rpow_five_twelfths_mul_seven_twelfths
    {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ ((5 : ℝ) / 12) * (N : ℝ) ^ ((7 : ℝ) / 12) = N := by
  rw [← Real.rpow_add (by positivity)]
  norm_num

private lemma rpow_one_sixth_mul_one_fourth {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ ((1 : ℝ) / 6) * (N : ℝ) ^ ((1 : ℝ) / 4) =
      (N : ℝ) ^ ((5 : ℝ) / 12) := by
  rw [← Real.rpow_add (by positivity)]
  congr 2
  norm_num

/-- The block scale gives a restricted-sum progression longer than the
`3 N^(5/6)` target, with the literal extraction constant `10^-8`. -/
theorem dfBlockSize_long_bound {N : ℕ} (hN : 1 ≤ N) :
    3 * (N : ℝ) ^ ((5 : ℝ) / 6) <
      (10 : ℝ) ^ (-8 : ℤ) * (dfBlockSize N : ℝ) ^ 2 := by
  let p : ℝ := (N : ℝ) ^ ((5 : ℝ) / 12)
  have hp : 0 < p := Real.rpow_pos_of_pos (by positivity) _
  have hL : 19000 * p ≤ (dfBlockSize N : ℝ) := by
    simpa [p] using dfBlockSize_cast_ge hN
  have hsq : (19000 * p) ^ 2 ≤ (dfBlockSize N : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hL
  have hp2 : p * p = (N : ℝ) ^ ((5 : ℝ) / 6) := by
    simpa [p] using rpow_five_twelfths_mul_self (show 0 < N by omega)
  norm_num [zpow_neg, pow_two] at *
  nlinarith

/-- The exceptional block and residue repetitions fit under the published
`10^5 N^(5/12)` exceptional-set budget. -/
theorem df_exceptional_budget {N : ℕ} (hN : 1 ≤ N) :
    3 * (dfResidueScale N : ℝ) ^ 2 + (dfBlockSize N : ℝ) ≤
      10 ^ (5 : ℕ) * (N : ℝ) ^ ((5 : ℝ) / 12) := by
  let p : ℝ := (N : ℝ) ^ ((5 : ℝ) / 12)
  let r : ℝ := (N : ℝ) ^ ((1 : ℝ) / 6)
  have hp : 0 ≤ p := Real.rpow_nonneg (by positivity) _
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hR : (dfResidueScale N : ℝ) ≤ r := by
    simpa [r] using dfResidueScale_cast_le N
  have hR2 : (dfResidueScale N : ℝ) ^ 2 ≤ r ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hR
  have hr2 : r ^ 2 = (N : ℝ) ^ ((1 : ℝ) / 3) := by
    simpa [r] using rpow_one_sixth_sq (show 0 < N by omega)
  have hsmall : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ p := by
    dsimp [p]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
  have hL : (dfBlockSize N : ℝ) ≤ 20000 * p := by
    simpa [p] using dfBlockSize_cast_le N
  norm_num at *
  nlinarith

/-- The central truncation, two residue-error blocks, and original DF95 block
fit within the published `10^5 N^(5/12)` exceptional budget. -/
theorem df_central_exceptional_budget {N : ℕ} (hN : 1 ≤ N) :
    (dfBlockSize N : ℝ) + 2 * (dfResidueScale N : ℝ) ^ 2 +
        2 * (dfCentralScale N : ℝ) ≤
      10 ^ (5 : ℕ) * (N : ℝ) ^ ((5 : ℝ) / 12) := by
  have hL := dfBlockSize_cast_le N
  have hR := dfResidueScale_cast_le N
  have hR2 : (dfResidueScale N : ℝ) ^ 2 ≤
      (N : ℝ) ^ ((1 : ℝ) / 3) := by
    have hs := (sq_le_sq₀ (by positivity) (by positivity)).2 hR
    rw [rpow_one_sixth_sq (show 0 < N by omega)] at hs
    exact hs
  have hp13 : (N : ℝ) ^ ((1 : ℝ) / 3) ≤
      (N : ℝ) ^ ((5 : ℝ) / 12) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
  have hT := dfCentralScale_cast_le N
  norm_num at *
  nlinarith

/-- The product of the rounded central and short scales has enough room for
the `9N/4` comparison whenever the available long progression has its
published `3 N^(5/6)` length. -/
theorem eventually_nine_mul_lt_four_mul_central_min_short :
    ∀ᶠ N : ℕ in atTop, ∀ longLength : ℕ,
      3 * (N : ℝ) ^ ((5 : ℝ) / 6) ≤ (longLength : ℝ) →
      9 * N < 4 * (dfCentralScale N * min (dfShortScale N) longLength) := by
  filter_upwards [eventually_dfCentralScale_cast_ge,
      eventually_dfShortScale_cast_ge, eventually_ge_atTop 1] with
      N hT hU hN longLength hlong
  have hshortLong : dfShortScale N ≤ longLength := by
    have hUupper := dfShortScale_cast_le N
    have hpow : (N : ℝ) ^ ((7 : ℝ) / 12) ≤
        (N : ℝ) ^ ((5 : ℝ) / 6) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
    exact_mod_cast (show (dfShortScale N : ℝ) ≤ longLength by
      have hq : 0 ≤ (N : ℝ) ^ ((5 : ℝ) / 6) := by positivity
      nlinarith)
  rw [Nat.min_eq_left hshortLong]
  have hmul := mul_le_mul hT hU (by positivity) (by positivity)
  have hpowprod := rpow_five_twelfths_mul_seven_twelfths
    (show 0 < N by omega)
  have hreal : (9 : ℝ) * N <
      4 * ((dfCentralScale N : ℝ) * (dfShortScale N : ℝ)) := by
    have hNpos : (0 : ℝ) < N := by positivity
    nlinarith
  exact_mod_cast hreal

/-- The alignment scale eventually dominates twice the residue scale. -/
theorem eventually_two_mul_dfResidueScale_lt_dfAlignmentScale :
    ∀ᶠ N : ℕ in atTop,
      2 * dfResidueScale N < dfAlignmentScale N := by
  have habs := eventually_const_mul_rpow_le_rpow
    (C := (3 : ℝ)) (a := (1 : ℝ) / 6) (b := (1 : ℝ) / 4)
      (by norm_num) (by norm_num)
  filter_upwards [habs, eventually_dfAlignmentScale_cast_ge,
      eventually_ge_atTop 1] with N habs hT hN
  have hR := dfResidueScale_cast_le N
  have hu : 0 < (N : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have hreal : (2 : ℝ) * dfResidueScale N < dfAlignmentScale N := by
    nlinarith
  exact_mod_cast hreal

/-- Stronger form used by the alignment repair. -/
theorem eventually_four_mul_dfResidueScale_lt_dfAlignmentScale :
    ∀ᶠ N : ℕ in atTop,
      4 * dfResidueScale N < dfAlignmentScale N := by
  have habs := eventually_const_mul_rpow_le_rpow
    (C := (5 : ℝ)) (a := (1 : ℝ) / 6) (b := (1 : ℝ) / 4)
      (by norm_num) (by norm_num)
  filter_upwards [habs, eventually_dfAlignmentScale_cast_ge,
      eventually_ge_atTop 1] with N habs hT hN
  have hR := dfResidueScale_cast_le N
  have hu : 0 < (N : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have hreal : (4 : ℝ) * dfResidueScale N < dfAlignmentScale N := by
    nlinarith
  exact_mod_cast hreal

/-- The product of the residue and alignment floors is bounded by the
`N^(5/12)` exceptional scale. -/
theorem dfResidueScale_mul_dfAlignmentScale_le {N : ℕ} (hN : 1 ≤ N) :
    ((dfResidueScale N * dfAlignmentScale N : ℕ) : ℝ) ≤
      (N : ℝ) ^ ((5 : ℝ) / 12) := by
  have hR := dfResidueScale_cast_le N
  have hT := dfAlignmentScale_cast_le N
  have hmul := mul_le_mul hR hT (by positivity) (by positivity)
  have hpow := rpow_one_sixth_mul_one_fourth (show 0 < N by omega)
  push_cast
  exact hmul.trans_eq hpow

/-- The raw progression engine has the requested `7/2` slack below its
limiting constant `4`. -/
theorem dfBlockSize_engine_slack {N : ℕ} (hN : 1 ≤ N) :
    (7 : ℝ) / 2 * (N : ℝ) ^ ((5 : ℝ) / 6) ≤
      (10 : ℝ) ^ (-8 : ℤ) * (dfBlockSize N : ℝ) ^ 2 := by
  have hL : 19000 * (N : ℝ) ^ ((5 : ℝ) / 12) ≤
      (dfBlockSize N : ℝ) := dfBlockSize_cast_ge hN
  have hsq : (19000 * (N : ℝ) ^ ((5 : ℝ) / 12)) ^ 2 ≤
      (dfBlockSize N : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hL
  have hp2 := rpow_five_twelfths_mul_self (show 0 < N by omega)
  norm_num [zpow_neg, pow_two] at *
  nlinarith

/-- Sharpened raw-engine slack used by the alignment repair. -/
theorem dfBlockSize_engine_slack_eighteen_fifths {N : ℕ} (hN : 1 ≤ N) :
    (18 : ℝ) / 5 * (N : ℝ) ^ ((5 : ℝ) / 6) ≤
      (10 : ℝ) ^ (-8 : ℤ) * (dfBlockSize N : ℝ) ^ 2 := by
  have hL : 19000 * (N : ℝ) ^ ((5 : ℝ) / 12) ≤
      (dfBlockSize N : ℝ) := dfBlockSize_cast_ge hN
  have hsq : (19000 * (N : ℝ) ^ ((5 : ℝ) / 12)) ^ 2 ≤
      (dfBlockSize N : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hL
  have hp2 := rpow_five_twelfths_mul_self (show 0 < N by omega)
  norm_num [zpow_neg, pow_two] at *
  nlinarith

/-- A concrete dyadic-generator bound.  The constant `36` follows from
`log 2 > 0.693` and `log x ≤ 24 x^(1/24)`. -/
theorem natLog_two_cast_le_thirtysix_rpow {N : ℕ} (hN : 1 ≤ N) :
    (Nat.log 2 N : ℝ) ≤ 36 * (N : ℝ) ^ ((1 : ℝ) / 24) := by
  have hNne : N ≠ 0 := by omega
  have hpowNat : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hNne
  have hpowReal : (2 : ℝ) ^ Nat.log 2 N ≤ (N : ℝ) := by exact_mod_cast hpowNat
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 N)
    hpowReal
  rw [Real.log_pow] at hlog
  have hlogUpper := Real.log_le_rpow_div (Nat.cast_nonneg N)
    (show (0 : ℝ) < (1 : ℝ) / 24 by norm_num)
  have hlog2 : (2 : ℝ) / 3 < Real.log 2 :=
    (show (2 : ℝ) / 3 < 0.6931471803 by norm_num).trans Real.log_two_gt_d9
  have hmulLower : (2 : ℝ) / 3 * Nat.log 2 N ≤
      (Nat.log 2 N : ℝ) * Real.log 2 := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hlog2.le
        (Nat.cast_nonneg (Nat.log 2 N) : (0 : ℝ) ≤ Nat.log 2 N))
  nlinarith

/-- Version of the dyadic-generator bound with the harmless `N+1` used by
the alignment construction. -/
theorem natLog_two_succ_cast_le_seventytwo_rpow {N : ℕ} (hN : 1 ≤ N) :
    (Nat.log 2 (N + 1) : ℝ) ≤
      72 * (N : ℝ) ^ ((1 : ℝ) / 24) := by
  have hbase := natLog_two_cast_le_thirtysix_rpow
    (N := N + 1) (show 1 ≤ N + 1 by omega)
  have hNtwo : ((N + 1 : ℕ) : ℝ) ≤ 2 * N := by
    exact_mod_cast (show N + 1 ≤ 2 * N by omega)
  have hrpow := Real.rpow_le_rpow (by positivity) hNtwo
    (show (0 : ℝ) ≤ (1 : ℝ) / 24 by norm_num)
  have htwo : (2 : ℝ) ^ ((1 : ℝ) / 24) ≤ 2 := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
        (by norm_num) (show (1 : ℝ) / 24 ≤ 1 by norm_num))
  rw [Real.mul_rpow (by positivity) (by positivity)] at hrpow
  have hp0 : 0 ≤ (N : ℝ) ^ ((1 : ℝ) / 24) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right htwo hp0]

/-- A logarithmic number of generators, each using one alignment block, has
total size at most `N^(5/12)`. -/
theorem eventually_two_mul_log_generators_alignment_le :
    ∀ᶠ N : ℕ in atTop, ∀ generators : ℕ,
      generators ≤ Nat.log 2 N →
      ((2 * generators * dfAlignmentScale N : ℕ) : ℝ) ≤
        (N : ℝ) ^ ((5 : ℝ) / 12) := by
  have habs := eventually_const_mul_rpow_le_rpow
    (C := (72 : ℝ)) (a := (7 : ℝ) / 24) (b := (5 : ℝ) / 12)
      (by norm_num) (by norm_num)
  filter_upwards [habs, eventually_ge_atTop 1] with N habs hN generators hgen
  have hk : (generators : ℝ) ≤ 36 * (N : ℝ) ^ ((1 : ℝ) / 24) := by
    have hgenReal : (generators : ℝ) ≤ Nat.log 2 N := by exact_mod_cast hgen
    exact hgenReal.trans (natLog_two_cast_le_thirtysix_rpow hN)
  have hT := dfAlignmentScale_cast_le N
  have hmul := mul_le_mul hk hT (by positivity) (by positivity)
  have hpow : (N : ℝ) ^ ((1 : ℝ) / 24) *
      (N : ℝ) ^ ((1 : ℝ) / 4) = (N : ℝ) ^ ((7 : ℝ) / 24) := by
    rw [← Real.rpow_add (by positivity)]
    congr 2
    norm_num
  push_cast
  nlinarith

/-- Base-fibre room: a dyadic number of alignment blocks is eventually at
most `N^(1/3)`. -/
theorem eventually_log_succ_generators_alignment_le_one_third :
    ∀ᶠ N : ℕ in atTop, ∀ generators : ℕ,
      generators ≤ Nat.log 2 (N + 1) →
      ((generators * dfAlignmentScale N : ℕ) : ℝ) ≤
        (N : ℝ) ^ ((1 : ℝ) / 3) := by
  have habs := eventually_const_mul_rpow_le_rpow
    (C := (72 : ℝ)) (a := (7 : ℝ) / 24) (b := (1 : ℝ) / 3)
      (by norm_num) (by norm_num)
  filter_upwards [habs, eventually_ge_atTop 1] with N habs hN generators hgen
  have hgenReal : (generators : ℝ) ≤ Nat.log 2 (N + 1) := by exact_mod_cast hgen
  have hk := hgenReal.trans (natLog_two_succ_cast_le_seventytwo_rpow hN)
  have hT := dfAlignmentScale_cast_le N
  have hmul := mul_le_mul hk hT (by positivity) (by positivity)
  have hpow : (N : ℝ) ^ ((1 : ℝ) / 24) *
      (N : ℝ) ^ ((1 : ℝ) / 4) = (N : ℝ) ^ ((7 : ℝ) / 24) := by
    rw [← Real.rpow_add (by positivity)]
    congr 2
    norm_num
  push_cast
  nlinarith

/-- Alignment-loss scale: a dyadic number of `N^(3/4)` losses is eventually
absorbed by `N^(5/6)`. -/
theorem eventually_log_succ_generators_three_fourths_le_five_sixths :
    ∀ᶠ N : ℕ in atTop, ∀ generators : ℕ,
      generators ≤ Nat.log 2 (N + 1) →
      (generators : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4) ≤
        (N : ℝ) ^ ((5 : ℝ) / 6) := by
  have habs := eventually_const_mul_rpow_le_rpow
    (C := (72 : ℝ)) (a := (19 : ℝ) / 24) (b := (5 : ℝ) / 6)
      (by norm_num) (by norm_num)
  filter_upwards [habs, eventually_ge_atTop 1] with N habs hN generators hgen
  have hgenReal : (generators : ℝ) ≤ Nat.log 2 (N + 1) := by exact_mod_cast hgen
  have hk := hgenReal.trans (natLog_two_succ_cast_le_seventytwo_rpow hN)
  have hpow : (N : ℝ) ^ ((1 : ℝ) / 24) *
      (N : ℝ) ^ ((3 : ℝ) / 4) = (N : ℝ) ^ ((19 : ℝ) / 24) := by
    rw [← Real.rpow_add (by positivity)]
    congr 2
    norm_num
  have hmul := mul_le_mul_of_nonneg_right hk
    (show 0 ≤ (N : ℝ) ^ ((3 : ℝ) / 4) by positivity)
  calc
    (generators : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 4) ≤
        (72 * (N : ℝ) ^ ((1 : ℝ) / 24)) *
          (N : ℝ) ^ ((3 : ℝ) / 4) := hmul
    _ = 72 * (N : ℝ) ^ ((19 : ℝ) / 24) := by rw [mul_assoc, hpow]
    _ ≤ (N : ℝ) ^ ((5 : ℝ) / 6) := habs

/-- Two alignment blocks per dyadic generator are absorbed by the
`N^(5/12)` exceptional scale. -/
theorem eventually_two_mul_log_succ_generators_alignment_le :
    ∀ᶠ N : ℕ in atTop, ∀ generators : ℕ,
      generators ≤ Nat.log 2 (N + 1) →
      ((2 * generators * dfAlignmentScale N : ℕ) : ℝ) ≤
        (N : ℝ) ^ ((5 : ℝ) / 12) := by
  have habs := eventually_const_mul_rpow_le_rpow
    (C := (144 : ℝ)) (a := (7 : ℝ) / 24) (b := (5 : ℝ) / 12)
      (by norm_num) (by norm_num)
  filter_upwards [habs, eventually_ge_atTop 1] with N habs hN generators hgen
  have hgenReal : (generators : ℝ) ≤ Nat.log 2 (N + 1) := by exact_mod_cast hgen
  have hk := hgenReal.trans (natLog_two_succ_cast_le_seventytwo_rpow hN)
  have hT := dfAlignmentScale_cast_le N
  have hmul := mul_le_mul hk hT (by positivity) (by positivity)
  have hpow : (N : ℝ) ^ ((1 : ℝ) / 24) *
      (N : ℝ) ^ ((1 : ℝ) / 4) = (N : ℝ) ^ ((7 : ℝ) / 24) := by
    rw [← Real.rpow_add (by positivity)]
    congr 2
    norm_num
  push_cast
  nlinarith

/-- Complete alignment-exception budget: the original engine block, residue
alignment, dyadic generators, and two central endpoint blocks all fit under
the published `10^5 N^(5/12)` allowance. -/
theorem eventually_df_alignment_exception_budget :
    ∀ᶠ N : ℕ in atTop, ∀ generators : ℕ,
      generators ≤ Nat.log 2 (N + 1) →
      ((dfBlockSize N + dfResidueScale N * dfAlignmentScale N +
          2 * generators * dfAlignmentScale N +
          2 * dfCentralScale N : ℕ) : ℝ) ≤
        10 ^ (5 : ℕ) * (N : ℝ) ^ ((5 : ℝ) / 12) := by
  filter_upwards [eventually_two_mul_log_succ_generators_alignment_le,
      eventually_ge_atTop 1] with N hgenAlign hN generators hgen
  have hL := dfBlockSize_cast_le N
  have hRF := dfResidueScale_mul_dfAlignmentScale_le hN
  have hgF := hgenAlign generators hgen
  have hT := dfCentralScale_cast_le N
  push_cast at hRF hgF
  push_cast
  norm_num at hL ⊢
  nlinarith

/-- Quotient form of the alignment-loss estimate used in the repaired
modular argument. -/
theorem eventually_nine_mul_log_succ_mul_id_div_alignment_le_half_long :
    ∀ᶠ N : ℕ in atTop, ∀ generators : ℕ,
      generators ≤ Nat.log 2 (N + 1) →
      9 * (generators : ℝ) * N / (dfAlignmentScale N : ℝ) ≤
        (1 : ℝ) / 2 * (N : ℝ) ^ ((5 : ℝ) / 6) := by
  have habs := eventually_const_mul_rpow_le_rpow
    (C := (1440 : ℝ)) (a := (25 : ℝ) / 24) (b := (13 : ℝ) / 12)
      (by norm_num) (by norm_num)
  filter_upwards [habs, eventually_dfAlignmentScale_cast_ge,
      eventually_ge_atTop 1] with N habs hT hN generators hgen
  have hgenReal : (generators : ℝ) ≤ Nat.log 2 (N + 1) := by exact_mod_cast hgen
  have hk := hgenReal.trans (natLog_two_succ_cast_le_seventytwo_rpow hN)
  have hpN : (N : ℝ) ^ ((1 : ℝ) / 24) * N =
      (N : ℝ) ^ ((25 : ℝ) / 24) := by
    rw [← Real.rpow_add_one (by positivity)]
    norm_num
  have huq : (N : ℝ) ^ ((1 : ℝ) / 4) *
      (N : ℝ) ^ ((5 : ℝ) / 6) =
      (N : ℝ) ^ ((13 : ℝ) / 12) := by
    rw [← Real.rpow_add (by positivity)]
    congr 2
    norm_num
  have hleft : 18 * (generators : ℝ) * N ≤
      1296 * (N : ℝ) ^ ((25 : ℝ) / 24) := by
    have hmul := mul_le_mul_of_nonneg_right hk (show (0 : ℝ) ≤ N by positivity)
    nlinarith
  have hright : (9 : ℝ) / 10 * (N : ℝ) ^ ((13 : ℝ) / 12) ≤
      (dfAlignmentScale N : ℝ) * (N : ℝ) ^ ((5 : ℝ) / 6) := by
    have hmul := mul_le_mul_of_nonneg_right hT
      (show 0 ≤ (N : ℝ) ^ ((5 : ℝ) / 6) by positivity)
    nlinarith
  have hcross : 18 * (generators : ℝ) * N ≤
      (dfAlignmentScale N : ℝ) * (N : ℝ) ^ ((5 : ℝ) / 6) := by
    nlinarith
  have hFpos : (0 : ℝ) < dfAlignmentScale N := by
    have hu : 0 < (N : ℝ) ^ ((1 : ℝ) / 4) := by positivity
    linarith
  rw [div_le_iff₀ hFpos]
  nlinarith

/-- The aligned family retains more translation capacity than twice the
`9N/4` small-layer bound. -/
theorem eventually_alignment_capacity_margin :
    ∀ᶠ N : ℕ in atTop,
      2 * ((9 : ℝ) / 4 * N) <
        ((dfAlignmentScale N : ℝ) / 2) *
          ((18 : ℝ) / 5 * (N : ℝ) ^ ((5 : ℝ) / 6)) := by
  have habs := eventually_const_mul_rpow_le_rpow
    (C := (3 : ℝ)) (a := (1 : ℝ)) (b := (13 : ℝ) / 12)
      (by norm_num) (by norm_num)
  filter_upwards [habs, eventually_dfAlignmentScale_cast_ge,
      eventually_ge_atTop 1] with N habs hT hN
  have huq : (N : ℝ) ^ ((1 : ℝ) / 4) *
      (N : ℝ) ^ ((5 : ℝ) / 6) =
      (N : ℝ) ^ ((13 : ℝ) / 12) := by
    rw [← Real.rpow_add (by positivity)]
    congr 2
    norm_num
  have hmul := mul_le_mul_of_nonneg_right hT
    (show 0 ≤ (N : ℝ) ^ ((5 : ℝ) / 6) by positivity)
  have hNpos : (0 : ℝ) < N := by positivity
  have hTq : (9 : ℝ) / 10 * (N : ℝ) ^ ((13 : ℝ) / 12) ≤
      (dfAlignmentScale N : ℝ) * (N : ℝ) ^ ((5 : ℝ) / 6) := by
    nlinarith
  have habs' : (3 : ℝ) * N ≤ (N : ℝ) ^ ((13 : ℝ) / 12) := by
    simpa [Real.rpow_one] using habs
  rw [show ((dfAlignmentScale N : ℝ) / 2) *
      ((18 : ℝ) / 5 * (N : ℝ) ^ ((5 : ℝ) / 6)) =
      (9 : ℝ) / 5 * ((dfAlignmentScale N : ℝ) *
        (N : ℝ) ^ ((5 : ℝ) / 6)) by ring]
  calc
    2 * ((9 : ℝ) / 4 * N) < (243 : ℝ) / 50 * N := by nlinarith
    _ ≤ (81 : ℝ) / 50 * (N : ℝ) ^ ((13 : ℝ) / 12) := by
      rw [show (243 : ℝ) / 50 * N = (81 : ℝ) / 50 * (3 * N) by ring]
      exact mul_le_mul_of_nonneg_left habs' (by norm_num)
    _ ≤ (9 : ℝ) / 5 * ((dfAlignmentScale N : ℝ) *
        (N : ℝ) ^ ((5 : ℝ) / 6)) := by
      rw [show (81 : ℝ) / 50 * (N : ℝ) ^ ((13 : ℝ) / 12) =
        (9 : ℝ) / 5 * ((9 : ℝ) / 10 *
          (N : ℝ) ^ ((13 : ℝ) / 12)) by ring]
      exact mul_le_mul_of_nonneg_left hTq (by norm_num)

/-- Exact integral packing inequality for the aligned modular progression.
The term `2 * generators * layerCard` is the total translation loss, while
`F - 2R + 2` is the number of surviving aligned translates. -/
theorem eventually_df_alignment_aggregate_fit :
    ∀ᶠ N : ℕ in atTop, ∀ {layerCard generators longLength : ℕ},
      4 * layerCard < 9 * N →
      generators ≤ Nat.log 2 (N + 1) →
      (18 : ℝ) / 5 * (N : ℝ) ^ ((5 : ℝ) / 6) ≤ (longLength : ℝ) →
      2 * generators * layerCard +
          (dfAlignmentScale N - 2 * dfResidueScale N + 2) * dfLongTarget N ≤
        (dfAlignmentScale N - 2 * dfResidueScale N + 2) * longLength := by
  have hloss := eventually_nine_mul_log_succ_mul_id_div_alignment_le_half_long
  have hscale := eventually_four_mul_dfResidueScale_lt_dfAlignmentScale
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ ((5 : ℝ) / 6)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hpowTen : ∀ᶠ N : ℕ in atTop,
      10 ≤ (N : ℝ) ^ ((5 : ℝ) / 6) := tendsto_atTop.mp hpow 10
  filter_upwards [hloss, hscale, hpowTen, eventually_ge_atTop 1] with
      N hloss hscale hpowTen hN layerCard generators longLength
      hcard hgenerators hlong
  let F := dfAlignmentScale N
  let R := dfResidueScale N
  let G := F - 2 * R + 2
  let Q : ℝ := (N : ℝ) ^ ((5 : ℝ) / 6)
  have hFposNat : 0 < F := by dsimp [F]; omega
  have hFpos : (0 : ℝ) < F := by positivity
  have hloss' := hloss generators hgenerators
  have hcross : 18 * (generators : ℝ) * N ≤ (F : ℝ) * Q := by
    dsimp [F, Q]
    rw [div_le_iff₀ hFpos] at hloss'
    nlinarith
  have hcardReal : (4 : ℝ) * layerCard ≤ 9 * N := by
    exact_mod_cast hcard.le
  have hcardMul := mul_le_mul_of_nonneg_left hcardReal
    (show (0 : ℝ) ≤ 2 * generators by positivity)
  have hcost : ((2 * generators * layerCard : ℕ) : ℝ) ≤
      (F : ℝ) * Q / 4 := by
    push_cast
    nlinarith
  have hFGNat : F ≤ 2 * G := by
    dsimp [G, F, R]
    omega
  have hFG : (F : ℝ) ≤ 2 * G := by exact_mod_cast hFGNat
  have hcostG : ((2 * generators * layerCard : ℕ) : ℝ) ≤
      (G : ℝ) * Q / 2 := by
    have hQnonneg : 0 ≤ Q := by positivity
    have hmul := mul_le_mul_of_nonneg_right hFG hQnonneg
    nlinarith
  have htarget := dfLongTarget_cast_lt_add_one N
  have hgap : (dfLongTarget N : ℝ) + Q / 2 ≤ longLength := by
    dsimp [Q] at hpowTen hlong ⊢
    nlinarith
  have hgapMul := mul_le_mul_of_nonneg_left hgap
    (show (0 : ℝ) ≤ G by positivity)
  have hreal :
      ((2 * generators * layerCard + G * dfLongTarget N : ℕ) : ℝ) ≤
        ((G * longLength : ℕ) : ℝ) := by
    push_cast at hgapMul ⊢
    nlinarith
  simpa [F, R, G] using (show
    2 * generators * layerCard + G * dfLongTarget N ≤ G * longLength by
      exact_mod_cast hreal)

/-- All layer and complement room inequalities needed by the successive
support, order, alignment, and endpoint constructions.  The two displayed
dominant inequalities deliberately include every smaller overhead; callers
can discharge the individual finite-side conditions by `omega`. -/
theorem eventually_df_modular_room_dominant :
    ∀ᶠ N : ℕ in atTop, ∀ {card layer generators : ℕ},
      (49 / 25 : ℝ) * Real.sqrt N < (card : ℝ) →
      card / 10 ≤ layer → layer ≤ 3 * card / 4 →
      generators ≤ Nat.log 2 (N + 1) →
      let t := dfBlockSize N / 500000
      t + 1 + dfResidueScale N + dfResidueScale N ^ 2 +
          dfAlignmentScale N + generators * dfAlignmentScale N +
          dfCentralScale N ≤ layer ∧
        layer + dfBlockSize N +
          dfResidueScale N * dfAlignmentScale N +
          2 * generators * dfAlignmentScale N +
          2 * dfCentralScale N + 2 * dfResidueScale N ^ 2 +
          2 * dfAlignmentScale N + dfResidueScale N ≤ card := by
  have habs := eventually_const_mul_rpow_five_twelfths_le_sqrt
    1000000 (by norm_num)
  have hgenAll := eventually_log_succ_generators_alignment_le_one_third
  filter_upwards [habs, hgenAll, eventually_ge_atTop 1] with
      N habs hgenAll hN card layer generators hlarge hlower hupper hgenerators
  let p : ℝ := (N : ℝ) ^ ((5 : ℝ) / 12)
  let t := dfBlockSize N / 500000
  have hp : 0 ≤ p := by positivity
  have hpone : (1 : ℝ) ≤ p := by
    dsimp [p]
    exact Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hB : (dfBlockSize N : ℝ) ≤ 20000 * p := by
    simpa [p] using dfBlockSize_cast_le N
  have htNat : t ≤ dfBlockSize N := by
    dsimp [t]
    exact Nat.div_le_self _ _
  have ht : (t : ℝ) ≤ 20000 * p := by
    exact (by exact_mod_cast htNat : (t : ℝ) ≤ dfBlockSize N).trans hB
  have hR := dfResidueScale_cast_le N
  have hRpow : (N : ℝ) ^ ((1 : ℝ) / 6) ≤ p := by
    dsimp [p]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
  have hRp : (dfResidueScale N : ℝ) ≤ p := hR.trans hRpow
  have hR2 : (dfResidueScale N : ℝ) ^ 2 ≤ p := by
    have hs := (sq_le_sq₀ (by positivity) (by positivity)).2 hR
    rw [rpow_one_sixth_sq (show 0 < N by omega)] at hs
    exact hs.trans (by
      dsimp [p]
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hN) (by norm_num))
  have hF := dfAlignmentScale_cast_le N
  have hFp : (dfAlignmentScale N : ℝ) ≤ p := hF.trans (by
    dsimp [p]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN) (by norm_num))
  have hRF := dfResidueScale_mul_dfAlignmentScale_le hN
  have hgen := hgenAll generators hgenerators
  have hgenp : ((generators * dfAlignmentScale N : ℕ) : ℝ) ≤ p :=
    hgen.trans (by
      dsimp [p]
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hN) (by norm_num))
  have hT : (dfCentralScale N : ℝ) ≤ 3 * p := by
    simpa [p] using dfCentralScale_cast_le N
  push_cast at hgenp
  let firstOverhead : ℕ :=
    t + 1 + dfResidueScale N + dfResidueScale N ^ 2 +
      dfAlignmentScale N + generators * dfAlignmentScale N +
      dfCentralScale N
  have hfirstReal : (firstOverhead : ℝ) ≤ 100000 * p := by
    dsimp [firstOverhead]
    push_cast
    nlinarith
  have htenFirst : 10 * firstOverhead ≤ card := by
    have hreal : ((10 * firstOverhead : ℕ) : ℝ) < card := by
      calc
        ((10 * firstOverhead : ℕ) : ℝ) ≤ 1000000 * p := by
          push_cast
          nlinarith
        _ ≤ Real.sqrt N := by simpa [p] using habs
        _ < (49 / 25 : ℝ) * Real.sqrt N := by
          have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 (by positivity)
          nlinarith
        _ < card := hlarge
    exact_mod_cast hreal.le
  have hfirst : firstOverhead ≤ layer := by omega
  let secondOverhead : ℕ :=
    dfBlockSize N + dfResidueScale N * dfAlignmentScale N +
      2 * generators * dfAlignmentScale N + 2 * dfCentralScale N +
      2 * dfResidueScale N ^ 2 + 2 * dfAlignmentScale N +
      dfResidueScale N
  have hsecondReal : (secondOverhead : ℝ) ≤ 100000 * p := by
    dsimp [secondOverhead]
    push_cast at hRF hgenp ⊢
    nlinarith
  have hfourSecond : 4 * secondOverhead ≤ card := by
    have hreal : ((4 * secondOverhead : ℕ) : ℝ) < card := by
      calc
        ((4 * secondOverhead : ℕ) : ℝ) ≤ 1000000 * p := by
          push_cast
          nlinarith
        _ ≤ Real.sqrt N := by simpa [p] using habs
        _ < (49 / 25 : ℝ) * Real.sqrt N := by
          have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 (by positivity)
          nlinarith
        _ < card := hlarge
    exact_mod_cast hreal.le
  have hsecond : layer + secondOverhead ≤ card := by omega
  constructor
  · simpa [firstOverhead, t, add_assoc] using hfirst
  · simpa [secondOverhead, add_assoc] using hsecond

/-- Expanded room package in precisely the forms consumed by the finite
modular lemmas.  Here `t = B / 500000`; the first two clauses are the final
generator/endpoint rooms and the remaining clauses cover the earlier
support, order/subgroup, and single-generator alignment stages. -/
theorem eventually_df_modular_room :
    ∀ᶠ N : ℕ in atTop, ∀ {card layer generators : ℕ},
      (49 / 25 : ℝ) * Real.sqrt N < (card : ℝ) →
      card / 10 ≤ layer → layer ≤ 3 * card / 4 →
      generators ≤ Nat.log 2 (N + 1) →
      let t := dfBlockSize N / 500000
      t + generators * dfAlignmentScale N + dfCentralScale N ≤ layer ∧
      (layer - (t + generators * dfAlignmentScale N + dfCentralScale N)) +
          (dfBlockSize N + dfResidueScale N * dfAlignmentScale N +
            2 * generators * dfAlignmentScale N) +
          2 * dfCentralScale N ≤ card ∧
      t + 1 ≤ layer ∧
      (layer - (t + 1)) + dfResidueScale N ≤ card - dfBlockSize N ∧
      t + dfResidueScale N ≤ layer ∧
      (layer - (t + dfResidueScale N)) + 2 * dfResidueScale N ^ 2 ≤
        card - dfBlockSize N ∧
      t + dfResidueScale N ^ 2 ≤ layer ∧
      (layer - (t + dfResidueScale N ^ 2)) + 2 * dfResidueScale N ^ 2 ≤
        card - dfBlockSize N ∧
      t + dfAlignmentScale N ≤ layer ∧
      (layer - (t + dfAlignmentScale N)) + 2 * dfAlignmentScale N ≤
        card - dfBlockSize N := by
  filter_upwards [eventually_df_modular_room_dominant] with N hroom
  intro card layer generators hlarge hlower hupper hgenerators
  obtain ⟨hfirst, hsecond⟩ :=
    hroom hlarge hlower hupper hgenerators
  dsimp only at hfirst hsecond ⊢
  omega

/-- Endpoint room in the uniform form used before the actual number of
generators has been fixed.  In contrast to subtracting the generator blocks
from the layer, this remains valid when that number is zero. -/
theorem eventually_df_modular_uniform_endpoint_room :
    ∀ᶠ N : ℕ in atTop, ∀ {card layer generators : ℕ},
      (49 / 25 : ℝ) * Real.sqrt N < (card : ℝ) →
      card / 10 ≤ layer → layer ≤ 3 * card / 4 →
      generators ≤ Nat.log 2 (N + 1) →
      let t := dfBlockSize N / 500000
      (layer - (t + dfCentralScale N)) + 2 * dfCentralScale N +
          (dfBlockSize N + dfResidueScale N * dfAlignmentScale N +
            2 * generators * dfAlignmentScale N) ≤ card := by
  filter_upwards [eventually_df_modular_room_dominant] with N hroom
  intro card layer generators hlarge hlower hupper hgenerators
  obtain ⟨_hfirst, hsecond⟩ :=
    hroom hlarge hlower hupper hgenerators
  dsimp only at hsecond ⊢
  omega

/-- The rich base fibre still has strictly more mass than all residue and
dyadic-alignment selections.  The cubic residue term has leading constant
one at the square-root scale; every other term is `o(√N)`, leaving the
`1.96√N` window with ample room. -/
theorem eventually_df_alignment_mass_room :
    ∀ᶠ N : ℕ in atTop, ∀ {card generators : ℕ},
      (49 / 25 : ℝ) * Real.sqrt N < (card : ℝ) →
      generators ≤ Nat.log 2 (N + 1) →
      dfBlockSize N + dfResidueScale N * dfAlignmentScale N +
          dfResidueScale N *
            (dfResidueScale N ^ 2 + generators * dfAlignmentScale N) < card := by
  have hpabs := eventually_const_mul_rpow_five_twelfths_le_sqrt
    100000 (by norm_num)
  have hwabs := eventually_const_mul_rpow_eleven_twentyfourths_le_sqrt
    200 (by norm_num)
  filter_upwards [hpabs, hwabs, eventually_ge_atTop 1] with
      N hpabs hwabs hN card generators hlarge hgenerators
  let p : ℝ := (N : ℝ) ^ ((5 : ℝ) / 12)
  let w : ℝ := (N : ℝ) ^ ((11 : ℝ) / 24)
  let r : ℝ := (N : ℝ) ^ ((1 : ℝ) / 6)
  have hB : (dfBlockSize N : ℝ) ≤ 20000 * p := by
    simpa [p] using dfBlockSize_cast_le N
  have hRF := dfResidueScale_mul_dfAlignmentScale_le hN
  have hR : (dfResidueScale N : ℝ) ≤ r := by
    simpa [r] using dfResidueScale_cast_le N
  have hR3 : (dfResidueScale N : ℝ) ^ 3 ≤ Real.sqrt N := by
    have hs : (dfResidueScale N : ℝ) ^ 3 ≤ r ^ 3 := by gcongr
    rw [show r ^ 3 = Real.sqrt N by
      simpa [r] using rpow_one_sixth_cube (show 0 < N by omega)] at hs
    exact hs
  have hgenReal : (generators : ℝ) ≤
      72 * (N : ℝ) ^ ((1 : ℝ) / 24) := by
    exact (by exact_mod_cast hgenerators :
      (generators : ℝ) ≤ Nat.log 2 (N + 1)).trans
        (natLog_two_succ_cast_le_seventytwo_rpow hN)
  have hF := dfAlignmentScale_cast_le N
  have hgenF : (generators : ℝ) * dfAlignmentScale N ≤
      72 * (N : ℝ) ^ ((7 : ℝ) / 24) := by
    have hmul := mul_le_mul hgenReal hF (by positivity) (by positivity)
    have hpow : (N : ℝ) ^ ((1 : ℝ) / 24) *
        (N : ℝ) ^ ((1 : ℝ) / 4) =
          (N : ℝ) ^ ((7 : ℝ) / 24) := by
      rw [← Real.rpow_add (by positivity)]
      congr 2
      norm_num
    nlinarith
  have hRgenF : (dfResidueScale N : ℝ) *
      ((generators * dfAlignmentScale N : ℕ) : ℝ) ≤ 72 * w := by
    have hmul := mul_le_mul hR hgenF (by positivity) (by positivity)
    have hpow : (N : ℝ) ^ ((1 : ℝ) / 6) *
        (N : ℝ) ^ ((7 : ℝ) / 24) = w := by
      dsimp [w]
      rw [← Real.rpow_add (by positivity)]
      congr 2
      norm_num
    push_cast
    nlinarith
  have herr : 20001 * p + 72 * w ≤
      (57 : ℝ) / 100 * Real.sqrt N := by
    change 100000 * p ≤ Real.sqrt N at hpabs
    change 200 * w ≤ Real.sqrt N at hwabs
    have hp0 : 0 ≤ (N : ℝ) ^ ((5 : ℝ) / 12) := by positivity
    have hw0 : 0 ≤ (N : ℝ) ^ ((11 : ℝ) / 24) := by positivity
    nlinarith
  have hcast :
      ((dfBlockSize N + dfResidueScale N * dfAlignmentScale N +
          dfResidueScale N *
            (dfResidueScale N ^ 2 + generators * dfAlignmentScale N) : ℕ) : ℝ) ≤
        Real.sqrt N + 20001 * p + 72 * w := by
    push_cast at hRF hRgenF ⊢
    nlinarith
  have hfinal :
      ((dfBlockSize N + dfResidueScale N * dfAlignmentScale N +
          dfResidueScale N *
            (dfResidueScale N ^ 2 + generators * dfAlignmentScale N) : ℕ) : ℝ) <
        card := by
    calc
      _ ≤ Real.sqrt N + 20001 * p + 72 * w := hcast
      _ ≤ (157 : ℝ) / 100 * Real.sqrt N := by linarith
      _ < (49 / 25 : ℝ) * Real.sqrt N := by
        have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 (by positivity)
        nlinarith
      _ < card := hlarge
  exact_mod_cast hfinal

/-- Exact convex-translate margin: the surviving aligned translates contain
strictly more than twice the selected restricted layer. -/
theorem eventually_df_alignment_convex_margin :
    ∀ᶠ N : ℕ in atTop, ∀ {layerCard longLength : ℕ},
      4 * layerCard < 9 * N →
      (18 : ℝ) / 5 * (N : ℝ) ^ ((5 : ℝ) / 6) ≤ (longLength : ℝ) →
      2 * layerCard <
        (dfAlignmentScale N - 2 * dfResidueScale N + 2) * longLength := by
  filter_upwards [eventually_alignment_capacity_margin,
      eventually_four_mul_dfResidueScale_lt_dfAlignmentScale] with
      N hmargin hscale layerCard longLength hcard hlong
  let F := dfAlignmentScale N
  let R := dfResidueScale N
  let G := F - 2 * R + 2
  have hcardReal : (layerCard : ℝ) < (9 : ℝ) / 4 * N := by
    have hcast : (4 : ℝ) * layerCard < 9 * N := by exact_mod_cast hcard
    nlinarith
  have hfirst : (2 : ℝ) * layerCard <
      ((F : ℝ) / 2) *
        ((18 : ℝ) / 5 * (N : ℝ) ^ ((5 : ℝ) / 6)) := by
    have hcardTwo : (2 : ℝ) * layerCard <
        2 * ((9 : ℝ) / 4 * N) := by nlinarith
    exact hcardTwo.trans hmargin
  have hFGNat : F ≤ 2 * G := by
    dsimp [F, R, G]
    omega
  have hFG : (F : ℝ) / 2 ≤ G := by
    have hcast : (F : ℝ) ≤ 2 * G := by exact_mod_cast hFGNat
    nlinarith
  have hprod : ((F : ℝ) / 2) *
      ((18 : ℝ) / 5 * (N : ℝ) ^ ((5 : ℝ) / 6)) ≤
        (G : ℝ) * longLength := by
    exact mul_le_mul hFG hlong (by positivity) (by positivity)
  have hreal : ((2 * layerCard : ℕ) : ℝ) < ((G * longLength : ℕ) : ℝ) := by
    push_cast
    exact hfirst.trans_le hprod
  simpa [F, R, G] using (show 2 * layerCard < G * longLength by
    exact_mod_cast hreal)

/-- Eventual arithmetic for the endpoint-orientation repair in the central
extractor.  The constants match the deliberately generous bounds produced by
the extractor: `u ≤ 3 N^(11/24)`, `q ≤ 300009 N^(5/12)`, and
`R ≤ 400020 N^(11/24)`.  Besides the ordinary local-density room, the first
conclusion gives the stronger room that would remain valid after charging an
extra `q` holes.  The second conclusion is the exact natural-number endpoint
gap used by the orientation argument. -/
theorem eventually_central_orientation_thresholds :
    ∀ᶠ N : ℕ in atTop, ∀ {K u q R s T theta : ℕ},
      2 * Real.sqrt N - 2 ≤ (K : ℝ) →
      (u : ℝ) ≤ 3 * (N : ℝ) ^ ((11 : ℝ) / 24) →
      (q : ℝ) ≤ 300009 * (N : ℝ) ^ ((5 : ℝ) / 12) →
      (R : ℝ) ≤ 400020 * (N : ℝ) ^ ((11 : ℝ) / 24) →
      K = 2 * u + T → T = 2 * s + q + theta → theta ≤ 1 → 1 ≤ q →
      4 * (R + q) + 3 + q ≤ s ∧
        N - 1 + 2 * ((2 * R - 1) * q) < 2 * q * s * (T - s) := by
  have hwindow := eventually_const_mul_rpow_eleven_twentyfourths_le_sqrt
    7000000 (by norm_num)
  have hproduct := eventually_const_mul_rpow_le_rpow
    (C := (40 : ℝ) * 400020 * 300009)
    (a := (7 : ℝ) / 8) (b := (1 : ℝ)) (by norm_num) (by positivity)
  filter_upwards [hwindow, hproduct, eventually_ge_atTop 1] with
      N hwindow hproduct hN K u q R s T theta hK hu hq hR hKT hTs
      htheta hqpos
  let p : ℝ := (N : ℝ) ^ ((5 : ℝ) / 12)
  let w : ℝ := (N : ℝ) ^ ((11 : ℝ) / 24)
  change (u : ℝ) ≤ 3 * w at hu
  change (q : ℝ) ≤ 300009 * p at hq
  change (R : ℝ) ≤ 400020 * w at hR
  change 7000000 * w ≤ Real.sqrt N at hwindow
  simp only [Real.rpow_one] at hproduct
  have hp : 0 ≤ p := by positivity
  have hw : 0 ≤ w := by positivity
  have hpw : p ≤ w := by
    dsimp [p, w]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
  have hwone : (1 : ℝ) ≤ w := by
    dsimp [w]
    exact Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hsqrtPos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by positivity)
  have hsqrtSq : (Real.sqrt N) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hdecompNat : K = 2 * u + 2 * s + q + theta := by omega
  have hdecomp : (K : ℝ) = 2 * u + 2 * s + q + theta := by
    exact_mod_cast hdecompNat
  have hthetaReal : (theta : ℝ) ≤ 1 := by exact_mod_cast htheta
  have herr : (2 : ℝ) + 2 * (3 * w) + 300009 * p + 1 ≤
      Real.sqrt N / 10 := by
    nlinarith
  have hs : (9 : ℝ) / 10 * Real.sqrt N ≤ (s : ℝ) := by
    nlinarith
  have hlocalReal :
      ((4 * (R + q) + 3 + q : ℕ) : ℝ) ≤ Real.sqrt N / 2 := by
    push_cast
    nlinarith
  have hlocal : 4 * (R + q) + 3 + q ≤ s := by
    have hlocalToS :
        ((4 * (R + q) + 3 + q : ℕ) : ℝ) ≤ (s : ℝ) := by
      exact hlocalReal.trans (by nlinarith)
    exact_mod_cast hlocalToS
  have hwp : w * p = (N : ℝ) ^ ((7 : ℝ) / 8) := by
    dsimp [w, p]
    rw [← Real.rpow_add (by positivity)]
    congr 2
    norm_num
  have hRq : (R : ℝ) * q ≤
      (400020 : ℝ) * 300009 * (N : ℝ) ^ ((7 : ℝ) / 8) := by
    have hmul := mul_le_mul hR hq (by positivity) (by positivity)
    rw [← hwp]
    nlinarith
  have hRqSmall : (4 : ℝ) * R * q ≤ (N : ℝ) / 10 := by
    nlinarith
  have hTsub : T - s = s + q + theta := by omega
  have hsSquare : (81 : ℝ) / 100 * N ≤ (s : ℝ) ^ 2 := by
    have hsnonneg : (0 : ℝ) ≤ s := by positivity
    have hscalednonneg : 0 ≤ (9 : ℝ) / 10 * Real.sqrt N := by positivity
    have hsq := (sq_le_sq₀ hscalednonneg hsnonneg).2 hs
    nlinarith
  have hright : 2 * (s : ℝ) ^ 2 ≤
      ((2 * q * s * (T - s) : ℕ) : ℝ) := by
    have hqReal : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
    have hTsubLeNat : s ≤ T - s := by omega
    have hTsubLe : (s : ℝ) ≤ ((T - s : ℕ) : ℝ) := by exact_mod_cast hTsubLeNat
    have hbase0 := mul_le_mul hqReal hTsubLe
      (show (0 : ℝ) ≤ s by positivity) (show (0 : ℝ) ≤ q by positivity)
    have hbase : (s : ℝ) ≤ (q : ℝ) * ((T - s : ℕ) : ℝ) := by
      simpa only [one_mul] using hbase0
    have hmul := mul_le_mul_of_nonneg_right hbase
      (show (0 : ℝ) ≤ s by positivity)
    calc
      2 * (s : ℝ) ^ 2 = 2 * ((s : ℝ) * s) := by ring
      _ ≤ 2 * (((q : ℝ) * ((T - s : ℕ) : ℝ)) * s) := by gcongr
      _ = ((2 * q * s * (T - s) : ℕ) : ℝ) := by push_cast; ring
  have he : (2 * R - 1) * q ≤ 2 * R * q :=
    Nat.mul_le_mul_right q (Nat.sub_le _ _)
  have hleftNat :
      N - 1 + 2 * ((2 * R - 1) * q) ≤ N + 4 * R * q := by
    have htwoE : 2 * ((2 * R - 1) * q) ≤ 4 * R * q := by
      calc
        2 * ((2 * R - 1) * q) ≤ 2 * (2 * R * q) := Nat.mul_le_mul_left 2 he
        _ = 4 * R * q := by ring
    exact Nat.add_le_add (Nat.sub_le N 1) htwoE
  have hleft :
      ((N - 1 + 2 * ((2 * R - 1) * q) : ℕ) : ℝ) ≤
        (11 : ℝ) / 10 * N := by
    have hleftCast :
        ((N - 1 + 2 * ((2 * R - 1) * q) : ℕ) : ℝ) ≤
          ((N + 4 * R * q : ℕ) : ℝ) := by exact_mod_cast hleftNat
    have hsum : ((N + 4 * R * q : ℕ) : ℝ) ≤
        (11 : ℝ) / 10 * N := by
      push_cast
      linarith
    exact hleftCast.trans hsum
  constructor
  · exact hlocal
  · have hgapReal :
        ((N - 1 + 2 * ((2 * R - 1) * q) : ℕ) : ℝ) <
          ((2 * q * s * (T - s) : ℕ) : ℝ) := by
      have hNreal : (0 : ℝ) < N := by positivity
      calc
        _ ≤ (11 : ℝ) / 10 * N := hleft
        _ < (162 : ℝ) / 100 * N := by nlinarith
        _ = 2 * ((81 : ℝ) / 100 * N) := by ring
        _ ≤ 2 * (s : ℝ) ^ 2 := by gcongr
        _ ≤ ((2 * q * s * (T - s) : ℕ) : ℝ) := hright
    exact_mod_cast hgapReal

/-- Integer-cast form of the central endpoint-gap inequality. -/
theorem central_orientation_gap_int
    {N q R s T : ℕ}
    (hgap : N - 1 + 2 * ((2 * R - 1) * q) < 2 * q * s * (T - s)) :
    ((N - 1 : ℕ) : ℤ) + 2 * (((2 * R - 1) * q : ℕ) : ℤ) <
      2 * (q : ℤ) * s * ((T - s : ℕ) : ℤ) := by
  exact_mod_cast hgap

/-- Signed form used by the endpoint-orientation lemma.  This remains valid
when `R = 0`: natural subtraction truncates `2R-1` upward, so the natural
inequality is the stronger statement. -/
theorem central_orientation_signed_gap_int
    {N q R s T : ℕ} (hN : 1 ≤ N)
    (hgap : N - 1 + 2 * ((2 * R - 1) * q) < 2 * q * s * (T - s)) :
    (N : ℤ) - 1 + 2 * ((2 * (R : ℤ) - 1) * (q : ℤ)) <
      2 * (q : ℤ) * (s : ℤ) * ((T - s : ℕ) : ℤ) := by
  have hgapCast :
      ((N - 1 : ℕ) : ℤ) + 2 * (((2 * R - 1) * q : ℕ) : ℤ) <
        2 * (q : ℤ) * (s : ℤ) * ((T - s : ℕ) : ℤ) := by
    exact_mod_cast hgap
  rw [Nat.cast_sub hN] at hgapCast
  have hRcast :
      2 * (R : ℤ) - 1 ≤ ((2 * R - 1 : ℕ) : ℤ) := by
    cases R <;> simp <;> omega
  have hscaled := mul_le_mul_of_nonneg_right hRcast
    (show (0 : ℤ) ≤ q by positivity)
  push_cast at hgapCast
  nlinarith

/-- The extracted progression repeated over the residue scale has enough
capacity to cover the whole possible sum interval. -/
theorem eventually_df_repeated_long_capacity :
    ∀ᶠ N : ℕ in atTop,
      2 * N + 1 ≤ dfResidueScale N *
        Nat.floor ((10 : ℝ) ^ (-8 : ℤ) * (dfBlockSize N : ℝ) ^ 2) := by
  have hR := eventually_dfResidueScale_cast_ge
  have hq : Tendsto (fun N : ℕ => (N : ℝ) ^ ((5 : ℝ) / 6)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hq10 : ∀ᶠ N : ℕ in atTop,
      10 ≤ (N : ℝ) ^ ((5 : ℝ) / 6) := tendsto_atTop.mp hq 10
  filter_upwards [hR, hq10, eventually_ge_atTop 1] with N hR hq10 hN
  let q : ℝ := (N : ℝ) ^ ((5 : ℝ) / 6)
  let y : ℝ := (10 : ℝ) ^ (-8 : ℤ) * (dfBlockSize N : ℝ) ^ 2
  let T : ℕ := Nat.floor y
  have hy : 3 * q < y := by
    simpa [q, y] using dfBlockSize_long_bound hN
  have hL : 19000 * (N : ℝ) ^ ((5 : ℝ) / 12) ≤
      (dfBlockSize N : ℝ) := dfBlockSize_cast_ge hN
  have hp : 0 < (N : ℝ) ^ ((5 : ℝ) / 12) := by positivity
  have hsq : (19000 * (N : ℝ) ^ ((5 : ℝ) / 12)) ^ 2 ≤
      (dfBlockSize N : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hL
  have hp2 := rpow_five_twelfths_mul_self (show 0 < N by omega)
  have hy361 : (361 : ℝ) / 100 * q ≤ y := by
    dsimp [q, y]
    norm_num [zpow_neg, pow_two] at *
    nlinarith
  have hfloor := Nat.lt_floor_add_one y
  have hT : (7 : ℝ) / 2 * q ≤ (T : ℝ) := by
    dsimp [T]
    push_cast at hfloor
    nlinarith
  have hprod : (63 : ℝ) / 20 * (N : ℝ) ≤
      (dfResidueScale N : ℝ) * (T : ℝ) := by
    have hnonnegT : 0 ≤ (T : ℝ) := by positivity
    have hnonnegR : 0 ≤ (dfResidueScale N : ℝ) := by positivity
    have hmul := mul_le_mul hR hT (by positivity) (by positivity)
    have hrq := rpow_one_sixth_mul_five_sixths (show 0 < N by omega)
    dsimp [q] at hmul
    nlinarith
  have htarget : (2 * N + 1 : ℕ) ≤ dfResidueScale N * T := by
    exact_mod_cast (show (2 * N + 1 : ℝ) ≤
        (dfResidueScale N : ℝ) * (T : ℝ) by
      push_cast
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith)
  simpa [T, y] using htarget

/-- Stronger modular margin used when the preliminary cardinality estimate is
`K^2 ≤ 6N + O(K)`: the repeated extracted progression eventually has more
than `5N/2` terms. -/
theorem eventually_five_halves_lt_df_repeated_long :
    ∀ᶠ N : ℕ in atTop,
      (5 : ℝ) / 2 * N <
        (dfResidueScale N : ℝ) *
          Nat.floor ((10 : ℝ) ^ (-8 : ℤ) * (dfBlockSize N : ℝ) ^ 2) := by
  have hq : Tendsto (fun N : ℕ => (N : ℝ) ^ ((5 : ℝ) / 6)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hq10 : ∀ᶠ N : ℕ in atTop,
      10 ≤ (N : ℝ) ^ ((5 : ℝ) / 6) := tendsto_atTop.mp hq 10
  filter_upwards [eventually_dfResidueScale_cast_ge, hq10,
      eventually_ge_atTop 1] with N hR hq10 hN
  let q : ℝ := (N : ℝ) ^ ((5 : ℝ) / 6)
  let y : ℝ := (10 : ℝ) ^ (-8 : ℤ) * (dfBlockSize N : ℝ) ^ 2
  let T : ℕ := Nat.floor y
  have hy : 3 * q < y := by
    simpa [q, y] using dfBlockSize_long_bound hN
  have hfloor := Nat.lt_floor_add_one y
  have hT : (29 : ℝ) / 10 * q < (T : ℝ) := by
    dsimp [T]
    nlinarith
  have hmul := mul_le_mul hR hT.le (by positivity) (by positivity)
  have hrq := rpow_one_sixth_mul_five_sixths (show 0 < N by omega)
  have hNpos : (0 : ℝ) < N := by positivity
  dsimp [q, T, y] at hmul ⊢
  nlinarith

/-- Integral form of the `5N/2` modular margin. -/
theorem eventually_five_mul_lt_two_mul_df_repeated_long :
    ∀ᶠ N : ℕ in atTop,
      5 * N < 2 * (dfResidueScale N *
        Nat.floor ((10 : ℝ) ^ (-8 : ℤ) * (dfBlockSize N : ℝ) ^ 2)) := by
  filter_upwards [eventually_five_halves_lt_df_repeated_long] with N hN
  have hreal : (5 : ℝ) * N <
      2 * ((dfResidueScale N : ℝ) *
        Nat.floor ((10 : ℝ) ^ (-8 : ℤ) * (dfBlockSize N : ℝ) ^ 2)) := by
    calc
      (5 : ℝ) * N = 2 * ((5 : ℝ) / 2 * N) := by ring
      _ < 2 * ((dfResidueScale N : ℝ) *
          Nat.floor ((10 : ℝ) ^ (-8 : ℤ) * (dfBlockSize N : ℝ) ^ 2)) :=
        mul_lt_mul_of_pos_left hN (by norm_num)
  exact_mod_cast hreal

/-- The modular repetition margin needed by the adjusted DF95 argument: the
residue scale times the published `3 N^(5/6)` progression length eventually
exceeds `9N/4`. -/
theorem eventually_nine_fourths_lt_residue_mul_long :
    ∀ᶠ N : ℕ in atTop,
      (9 : ℝ) / 4 * N <
        (dfResidueScale N : ℝ) *
          (3 * (N : ℝ) ^ ((5 : ℝ) / 6)) := by
  filter_upwards [eventually_dfResidueScale_cast_ge,
      eventually_ge_atTop 1] with N hR hN
  have hq : 0 < (N : ℝ) ^ ((5 : ℝ) / 6) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hR hq.le
  have hrq := rpow_one_sixth_mul_five_sixths (show 0 < N by omega)
  have hbase : (9 : ℝ) / 10 * N ≤
      (dfResidueScale N : ℝ) * (N : ℝ) ^ ((5 : ℝ) / 6) := by
    nlinarith
  calc
    (9 : ℝ) / 4 * N < (27 : ℝ) / 10 * N := by
      have : (0 : ℝ) < N := by positivity
      nlinarith
    _ = 3 * ((9 : ℝ) / 10 * N) := by ring
    _ ≤ 3 * ((dfResidueScale N : ℝ) *
        (N : ℝ) ^ ((5 : ℝ) / 6)) := by gcongr
    _ = (dfResidueScale N : ℝ) *
        (3 * (N : ℝ) ^ ((5 : ℝ) / 6)) := by ring

/-- The DF95 blocks and residue repetitions occupy only `o(√N)` places, so
they fit inside every set in the `1.96√N` large-set window. -/
theorem eventually_df_scales_fit_large_window :
    ∀ᶠ N : ℕ in atTop, ∀ K : ℕ,
      (49 / 25 : ℝ) * Real.sqrt N < K →
      dfBlockSize N + 3 * dfResidueScale N ^ 2 + dfResidueScale N ≤ K := by
  have habs := eventually_const_mul_rpow_five_twelfths_le_sqrt 20004 (by norm_num)
  filter_upwards [habs, eventually_ge_atTop 1] with N habs hN
  intro K hK
  have hbudget := df_exceptional_budget hN
  have hR := dfResidueScale_cast_le N
  have hp1 : (N : ℝ) ^ ((1 : ℝ) / 6) ≤
      (N : ℝ) ^ ((5 : ℝ) / 12) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
  have hcast : ((dfBlockSize N + 3 * dfResidueScale N ^ 2 +
      dfResidueScale N : ℕ) : ℝ) ≤
      20004 * (N : ℝ) ^ ((5 : ℝ) / 12) := by
    have hL := dfBlockSize_cast_le N
    have hR2 : (dfResidueScale N : ℝ) ^ 2 ≤
        (N : ℝ) ^ ((1 : ℝ) / 3) := by
      have hs := (sq_le_sq₀ (by positivity) (by positivity)).2 hR
      rw [rpow_one_sixth_sq (show 0 < N by omega)] at hs
      exact hs
    have hp13 : (N : ℝ) ^ ((1 : ℝ) / 3) ≤
        (N : ℝ) ^ ((5 : ℝ) / 12) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
    push_cast
    norm_num at hL ⊢
    nlinarith
  have hlt : ((dfBlockSize N + 3 * dfResidueScale N ^ 2 +
      dfResidueScale N : ℕ) : ℝ) < K := by
    calc
      _ ≤ 20004 * (N : ℝ) ^ ((5 : ℝ) / 12) := hcast
      _ ≤ Real.sqrt N := habs
      _ < (49 / 25 : ℝ) * Real.sqrt N := by
        have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 (by positivity)
        nlinarith
      _ < K := hK
  exact_mod_cast hlt.le

/-- Strong room estimate used by the generalized few-residue filler: four
copies of the block, residue, and endpoint overhead still fit in every
`1.96√N`-large set. -/
theorem eventually_four_mul_df_scales_le_large_window :
    ∀ᶠ N : ℕ in atTop, ∀ K : ℕ,
      (49 / 25 : ℝ) * Real.sqrt N < K →
      4 * (dfBlockSize N + dfResidueScale N + 1) ≤ K := by
  have habs := eventually_const_mul_rpow_five_twelfths_le_sqrt
    80008 (by norm_num)
  filter_upwards [habs, eventually_ge_atTop 1] with N habs hN
  intro K hK
  have hL := dfBlockSize_cast_le N
  have hR := dfResidueScale_cast_le N
  have hRpow : (N : ℝ) ^ ((1 : ℝ) / 6) ≤
      (N : ℝ) ^ ((5 : ℝ) / 12) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
  have hpone : (1 : ℝ) ≤ (N : ℝ) ^ ((5 : ℝ) / 12) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hcast : ((4 * (dfBlockSize N + dfResidueScale N + 1) : ℕ) : ℝ) ≤
      80008 * (N : ℝ) ^ ((5 : ℝ) / 12) := by
    push_cast
    norm_num at hL ⊢
    nlinarith
  have hlt : ((4 * (dfBlockSize N + dfResidueScale N + 1) : ℕ) : ℝ) < K := by
    calc
      _ ≤ 80008 * (N : ℝ) ^ ((5 : ℝ) / 12) := hcast
      _ ≤ Real.sqrt N := habs
      _ < (49 / 25 : ℝ) * Real.sqrt N := by
        have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 (by positivity)
        nlinarith
      _ < K := hK
  exact_mod_cast hlt.le

/-- Rich-residue room estimate.  The cubic residue scale contributes one
square-root main term; all block and quadratic errors fit in the remaining
`0.96√N` margin. -/
theorem eventually_df_rich_scales_le_large_window :
    ∀ᶠ N : ℕ in atTop, ∀ K : ℕ,
      (49 / 25 : ℝ) * Real.sqrt N < K →
      dfBlockSize N + dfResidueScale N ^ 3 + dfResidueScale N ^ 2 ≤ K := by
  have habs := eventually_const_mul_rpow_five_twelfths_le_sqrt
    (200010 / 9 : ℝ) (by norm_num)
  filter_upwards [habs, eventually_ge_atTop 1] with N habs hN
  intro K hK
  let r : ℝ := (N : ℝ) ^ ((1 : ℝ) / 6)
  let p : ℝ := (N : ℝ) ^ ((5 : ℝ) / 12)
  have hR : (dfResidueScale N : ℝ) ≤ r := by
    simpa [r] using dfResidueScale_cast_le N
  have hR2 : (dfResidueScale N : ℝ) ^ 2 ≤
      (N : ℝ) ^ ((1 : ℝ) / 3) := by
    have hs := (sq_le_sq₀ (by positivity) (by positivity)).2 hR
    rw [show r ^ 2 = (N : ℝ) ^ ((1 : ℝ) / 3) by
      simpa [r] using rpow_one_sixth_sq (show 0 < N by omega)] at hs
    exact hs
  have hR3 : (dfResidueScale N : ℝ) ^ 3 ≤ Real.sqrt N := by
    have hs : (dfResidueScale N : ℝ) ^ 3 ≤ r ^ 3 := by gcongr
    rw [show r ^ 3 = Real.sqrt N by
      simpa [r] using rpow_one_sixth_cube (show 0 < N by omega)] at hs
    exact hs
  have hp13 : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ p := by
    dsimp [p]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
  have hL : (dfBlockSize N : ℝ) ≤ 20000 * p := by
    simpa [p] using dfBlockSize_cast_le N
  have herr : 20001 * p ≤ (9 : ℝ) / 10 * Real.sqrt N := by
    dsimp [p] at habs ⊢
    have hp0 : 0 ≤ (N : ℝ) ^ ((5 : ℝ) / 12) := by positivity
    nlinarith
  have hcast :
      ((dfBlockSize N + dfResidueScale N ^ 3 +
          dfResidueScale N ^ 2 : ℕ) : ℝ) ≤
        Real.sqrt N + 20001 * p := by
    push_cast
    norm_num at hL ⊢
    nlinarith
  have hlt :
      ((dfBlockSize N + dfResidueScale N ^ 3 +
          dfResidueScale N ^ 2 : ℕ) : ℝ) < K := by
    calc
      _ ≤ Real.sqrt N + 20001 * p := hcast
      _ ≤ Real.sqrt N + (9 : ℝ) / 10 * Real.sqrt N := by gcongr
      _ < (49 / 25 : ℝ) * Real.sqrt N := by
        have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 (by positivity)
        nlinarith
      _ < K := hK
  exact_mod_cast hlt.le

/-- The DF95 block is eventually at most one two-thousandth of every
cardinality in the large-set window. -/
theorem eventually_dfBlockSize_le_div_large_window :
    ∀ᶠ N : ℕ in atTop, ∀ K : ℕ,
      (49 / 25 : ℝ) * Real.sqrt N < K →
      dfBlockSize N ≤ K / 2000 := by
  have habs := eventually_const_mul_rpow_five_twelfths_le_sqrt
    40000000 (by norm_num)
  filter_upwards [habs, eventually_ge_atTop 1] with N habs hN
  intro K hK
  have hL := dfBlockSize_cast_le N
  have hmul : 2000 * dfBlockSize N ≤ K := by
    have hmulreal : (2000 : ℝ) * (dfBlockSize N : ℝ) < K := by
      push_cast
      calc
        (2000 : ℝ) * dfBlockSize N ≤
            40000000 * (N : ℝ) ^ ((5 : ℝ) / 12) := by nlinarith
        _ ≤ Real.sqrt N := habs
        _ < (49 / 25 : ℝ) * Real.sqrt N := by
          have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 (by positivity)
          nlinarith
        _ < K := hK
    exact_mod_cast hmulreal.le
  omega

/-! ## The exact DF95 layer-selection capacity -/

/-- Polynomial antiderivative of the quadratic weight `s(K-s)`, normalized
so that it equals the sum over `s < n` at natural arguments. -/
private def weightPrefix (K n : ℝ) : ℝ :=
  K * n * (n - 1) / 2 - n * (n - 1) * (2 * n - 1) / 6

private lemma sum_range_weight_eq_weightPrefix (K : ℝ) (n : ℕ) :
    ∑ s ∈ Finset.range n, (s : ℝ) * (K - s) = weightPrefix K n := by
  induction n with
  | zero => simp [weightPrefix]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      simp only [weightPrefix]
      ring

/-- Cast the natural weighted layer sum to the closed polynomial form. -/
private lemma cast_sum_Icc_weight_eq
    {K a b : ℕ} (hab : a ≤ b) (hbK : b ≤ K) :
    ((∑ s ∈ Finset.Icc a b, s * (K - s) : ℕ) : ℝ) =
      weightPrefix K (b + 1) - weightPrefix K a := by
  rw [Nat.cast_sum]
  have hcast : ∀ s ∈ Finset.Icc a b,
      ((s * (K - s) : ℕ) : ℝ) = (s : ℝ) * ((K : ℝ) - s) := by
    intro s hs
    simp only [Finset.mem_Icc] at hs
    rw [Nat.cast_mul, Nat.cast_sub (hs.2.trans hbK)]
  have hset : Finset.Icc a b = Finset.Ico a (b + 1) := by
    ext s
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  calc
    ∑ s ∈ Finset.Icc a b, ((s * (K - s) : ℕ) : ℝ) =
        ∑ s ∈ Finset.Icc a b, (s : ℝ) * ((K : ℝ) - s) :=
      Finset.sum_congr rfl hcast
    _ = ∑ s ∈ Finset.Ico a (b + 1), (s : ℝ) * ((K : ℝ) - s) := by rw [hset]
    _ = (∑ s ∈ Finset.range (b + 1), (s : ℝ) * ((K : ℝ) - s)) -
        ∑ s ∈ Finset.range a, (s : ℝ) * ((K : ℝ) - s) :=
      Finset.sum_Ico_eq_sub (f := fun s : ℕ =>
        (s : ℝ) * ((K : ℝ) - s)) (by omega)
    _ = weightPrefix K (b + 1) - weightPrefix K a := by
      rw [sum_range_weight_eq_weightPrefix, sum_range_weight_eq_weightPrefix]
      push_cast
      rfl

/-- On the range relevant to DF95, the prefix polynomial is increasing.
The deliberately generous `K ≥ 100` hypothesis makes the endpoint rounding
proof purely algebraic. -/
private lemma weightPrefix_mono_df_range
    {K x y : ℝ} (hK : 100 ≤ K)
    (hxlo : K / 10 - 1 ≤ x) (hxy : x ≤ y)
    (hyhi : y ≤ 3 * K / 4 + 1) :
    weightPrefix K x ≤ weightPrefix K y := by
  have hx : 0 ≤ x := by linarith
  have hy : 0 ≤ y := hx.trans hxy
  have hupper : 0 ≤ 3 * K / 4 + 1 - y := sub_nonneg.mpr hyhi
  have hdiff : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hxx : x ^ 2 ≤ x * y := by nlinarith [mul_nonneg hx hdiff]
  have hxyUpper : 4 * x * y ≤ (3 * K + 4) * x := by
    nlinarith [mul_nonneg hx hupper]
  have hyquad : 2 * y ^ 2 ≤ 3 * K * y := by
    have : 0 ≤ 3 * K - 2 * y := by nlinarith
    nlinarith [mul_nonneg hy this]
  have hbracket :
      0 ≤ 3 * K * (x + y - 1) -
        (2 * (x ^ 2 + x * y + y ^ 2) - 3 * (x + y) + 1) := by
    nlinarith
  have hfactor := mul_nonneg hdiff hbracket
  dsimp [weightPrefix]
  nlinarith [hfactor]

/-- Exact finite capacity inequality used by
`exists_df95_small_restricted_sum_layer`.  The large-set window alone implies
the inequality once `K` is beyond the harmless rounding threshold `1000`. -/
theorem df95_layer_capacity_of_large_window
    {N K : ℕ} (hKsize : 1000 ≤ K)
    (hwindow : (49 / 25 : ℝ) * Real.sqrt N < K) :
    25 * ((3 * K / 4) * N) <
      36 * ∑ s ∈ Finset.Icc (K / 10) (3 * K / 4), s * (K - s) := by
  let a : ℕ := K / 10
  let b : ℕ := 3 * K / 4
  have hab : a ≤ b := by dsimp [a, b]; omega
  have hbK : b ≤ K := by dsimp [b]; omega
  have hsum := cast_sum_Icc_weight_eq hab hbK
  let X : ℝ := K
  let A : ℝ := a
  let B : ℝ := b + 1
  have hX : 1000 ≤ X := by
    dsimp [X]
    exact_mod_cast hKsize
  have hAlo : X / 10 - 1 ≤ A := by
    have hdiv : K < 10 * (K / 10 + 1) := by omega
    dsimp [X, A, a]
    have hdivR : (K : ℝ) < 10 * ((K / 10 : ℕ) + 1) := by exact_mod_cast hdiv
    push_cast at hdivR
    linarith
  have hAle : A ≤ X / 10 := by
    have hdiv : 10 * (K / 10) ≤ K := by omega
    dsimp [X, A, a]
    have hdivR : (10 : ℝ) * (K / 10 : ℕ) ≤ K := by exact_mod_cast hdiv
    linarith
  have hBlo : 3 * X / 4 ≤ B := by
    have hdiv : 3 * K < 4 * (3 * K / 4 + 1) := by omega
    dsimp [X, B, b]
    have hdivR : (3 : ℝ) * K < 4 * ((3 * K / 4 : ℕ) + 1) := by
      exact_mod_cast hdiv
    push_cast at hdivR
    linarith
  have hBhi : B ≤ 3 * X / 4 + 1 := by
    have hdiv : 4 * (3 * K / 4) ≤ 3 * K := by omega
    dsimp [X, B, b]
    have hdivR : (4 : ℝ) * (3 * K / 4 : ℕ) ≤ 3 * K := by exact_mod_cast hdiv
    push_cast at hdivR
    linarith
  have hmonoA : weightPrefix X A ≤ weightPrefix X (X / 10) :=
    weightPrefix_mono_df_range (hX.trans' (by norm_num)) hAlo hAle (by nlinarith)
  have hmonoB : weightPrefix X (3 * X / 4) ≤ weightPrefix X B :=
    weightPrefix_mono_df_range (hX.trans' (by norm_num)) (by nlinarith) hBlo hBhi
  have hpoly :
      (3263 / 24000 : ℝ) * X ^ 3 - (39 / 800 : ℝ) * X ^ 2 -
          (13 / 120 : ℝ) * X =
        weightPrefix X (3 * X / 4) - weightPrefix X (X / 10) := by
    dsimp [weightPrefix]
    ring_nf
  have hsumLower :
      (3263 / 24000 : ℝ) * X ^ 3 - (39 / 800 : ℝ) * X ^ 2 -
          (13 / 120 : ℝ) * X ≤
        (∑ s ∈ Finset.Icc (K / 10) (3 * K / 4), s * (K - s) : ℕ) := by
    rw [hpoly]
    have h := sub_le_sub hmonoB hmonoA
    dsimp [X, A, B, a, b] at hsum h ⊢
    rw [hsum]
    exact h
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  have hsqrt : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hNnonneg
  have hwindowSq : (2401 / 625 : ℝ) * (N : ℝ) < X ^ 2 := by
    have hsumpos : 0 < (K : ℝ) + (49 / 25 : ℝ) * Real.sqrt N := by
      have hKpos : (0 : ℝ) < K := by positivity
      positivity
    have hprod := mul_pos (sub_pos.mpr hwindow) hsumpos
    dsimp [X]
    nlinarith
  have hbcast : ((3 * K / 4 : ℕ) : ℝ) ≤ 3 * X / 4 := by
    have hdiv : 4 * (3 * K / 4) ≤ 3 * K := by omega
    dsimp [X]
    have hdivR : (4 : ℝ) * (3 * K / 4 : ℕ) ≤ 3 * K := by exact_mod_cast hdiv
    linarith
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX
  have hreal :
      (25 : ℝ) * ((3 * K / 4 : ℕ) : ℝ) * N <
        36 * (∑ s ∈ Finset.Icc (K / 10) (3 * K / 4),
          s * (K - s) : ℕ) := by
    have hleft : (25 : ℝ) * ((3 * K / 4 : ℕ) : ℝ) * N ≤
        (75 / 4 : ℝ) * X * N := by
      have hmul := mul_le_mul_of_nonneg_right hbcast hNnonneg
      nlinarith
    have hmain : (75 / 4 : ℝ) * X * N <
        36 * ((3263 / 24000 : ℝ) * X ^ 3 -
          (39 / 800 : ℝ) * X ^ 2 - (13 / 120 : ℝ) * X) := by
      have hKN : (2401 / 625 : ℝ) * X * N < X ^ 3 := by
        have hmul := mul_lt_mul_of_pos_left hwindowSq hXpos
        nlinarith
      nlinarith
    nlinarith
  have hnat :
      25 * (3 * K / 4) * N <
        36 * ∑ s ∈ Finset.Icc (K / 10) (3 * K / 4), s * (K - s) := by
    exact_mod_cast hreal
  simpa [mul_assoc] using hnat

/-- Eventual form of the preceding exact capacity statement, ready to feed
directly to `exists_df95_small_restricted_sum_layer`. -/
theorem eventually_df95_layer_capacity :
    ∀ᶠ N : ℕ in atTop, ∀ K : ℕ,
      (49 / 25 : ℝ) * Real.sqrt N < K →
      25 * ((3 * K / 4) * N) <
        36 * ∑ s ∈ Finset.Icc (K / 10) (3 * K / 4), s * (K - s) := by
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop, 1000 ≤ Real.sqrt N :=
    tendsto_atTop.mp hsqrt 1000
  filter_upwards [hlarge] with N hN K hwindow
  have hK : 1000 ≤ K := by
    have : (1000 : ℝ) < K := by
      have hsqrt_nonneg := Real.sqrt_nonneg (N : ℝ)
      nlinarith
    exact_mod_cast this.le
  exact df95_layer_capacity_of_large_window hK hwindow

/-- A bound valid only beyond a finite threshold can be enlarged to a global
rough upper bound.  This is the precise finite-prefix absorption used when
packaging the DF95 estimate. -/
theorem roughUpperBound_of_eventually
    {N₀ : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℤ,
      IsBoundedAdmissible N A →
        (A.card : ℝ) ≤
          2 * Real.sqrt N + C * (N : ℝ) ^ ((5 : ℝ) / 12)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ N : ℕ, ∀ A : Finset ℤ, IsBoundedAdmissible N A →
        (A.card : ℝ) ≤
          2 * Real.sqrt N + C₀ * (N : ℝ) ^ ((5 : ℝ) / 12) := by
  refine ⟨C + N₀, by positivity, ?_⟩
  intro N A hA
  by_cases hNlarge : N₀ ≤ N
  · exact (h N hNlarge A hA).trans (by
      have hp : 0 ≤ (N : ℝ) ^ ((5 : ℝ) / 12) := Real.rpow_nonneg (by positivity) _
      gcongr
      exact le_add_of_nonneg_right (by positivity))
  · have hcard : A.card ≤ N := (card_le_k hA).trans (k_le N)
    by_cases hNzero : N = 0
    · subst N
      have hAzero : A.card = 0 := by omega
      simp [hAzero]
    · have hNpos : (0 : ℝ) < N := by positivity
      have hpow_one : 1 ≤ (N : ℝ) ^ ((5 : ℝ) / 12) :=
        Real.one_le_rpow (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hNzero))
          (by norm_num)
      have hNN₀ : N ≤ N₀ := by omega
      have hcast : (A.card : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hcard.trans hNN₀
      calc
        (A.card : ℝ) ≤ (N₀ : ℝ) := hcast
        _ ≤ (C + N₀) * (N : ℝ) ^ ((5 : ℝ) / 12) := by
          nlinarith [mul_le_mul_of_nonneg_left hpow_one (by positivity : (0 : ℝ) ≤ N₀)]
        _ ≤ 2 * Real.sqrt N +
              (C + N₀) * (N : ℝ) ^ ((5 : ℝ) / 12) := by
          linarith [Real.sqrt_nonneg (N : ℝ)]

end

end Erdos874
