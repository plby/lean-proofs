/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib

/-!
# Numerical parameters in the Liu--Montgomery argument

The published proof freely enlarges a number of absolute thresholds and
suppresses integer roundoff.  This file records the numerical facts needed to
make those choices literal.  The two scales used below are

* `lmOutputScale d = d / (10 * (log d)^12)`, the lower bound in the final
  even-cycle interval; and
* `lmPathScale n = n / (log n)^12`, the upper end of the exact-path window.

The floor used for a graph on `n` vertices is kept explicit.  In particular,
the lower path-window estimate below absorbs the loss caused by this floor.
The last section verifies that a sufficiently far tail of the powers of two
satisfies the growth hypothesis in Liu--Montgomery Corollary 1.3.
-/

open Filter Asymptotics

namespace Erdos63.Parameters

/-- Lower bound for the endpoint in Liu--Montgomery Theorem 1.1. -/
noncomputable def lmOutputScale (d : ℝ) : ℝ := d / (10 * Real.log d ^ 12)

/-- The upper endpoint of the exact-path range for an `n`-vertex graph. -/
noncomputable def lmPathScale (n : ℝ) : ℝ := n / Real.log n ^ 12

/-- Floor-safe natural endpoint for an `n`-vertex graph. -/
noncomputable def lmFloorEndpoint (n : ℕ) : ℕ :=
  ⌊ lmPathScale (n : ℝ) ⌋₊

/-- Radius used for the simple adjusters in the exact-path construction. -/
noncomputable def lmSimpleRadius (ε₁ : ℝ) (n : ℕ) : ℕ :=
  ⌈(400 / ε₁) * Real.log (n : ℝ) ^ 3⌉₊

/-- Radius used for the chained adjuster in the exact-path construction. -/
noncomputable def lmRadius (ε₁ : ℝ) (n : ℕ) : ℕ :=
  ⌈(1600 / ε₁) * Real.log (n : ℝ) ^ 3⌉₊

/-- Order of the protected vertex expansions in the exact-path proof. -/
noncomputable def lmExpansionOrder (n : ℕ) : ℕ :=
  ⌈Real.log (n : ℝ) ^ 10⌉₊

/-- A natural upper approximation to the ubiquitous factor `(log n)^3`. -/
noncomputable def lmLogCubeCeil (n : ℕ) : ℕ :=
  ⌈Real.log (n : ℝ) ^ 3⌉₊

/-- The short preliminary radius in the source proof of Lemma 3.11.  The
fifth power is the deliberately generous local scale used before the
ordinary `O(log n ^ 3)` connector growth begins. -/
noncomputable def lm311LocalRadius (n : ℕ) : ℕ :=
  ⌈2 * Real.log (Real.log (n : ℝ)) ^ 5⌉₊

/-- The denominator budget for adaptive stage `j` in the local Lemma 3.11
growth clock. -/
def lm311AdaptiveBlock (j : ℕ) : ℕ := 65536 * (j + 2) ^ 2

/-- Elapsed local-growth time after `j` factor-eight stages. -/
def lm311AdaptiveTime : ℕ → ℕ
  | 0 => 0
  | j + 1 => lm311AdaptiveTime j + 14 * lm311AdaptiveBlock j

/-- Number of factor-eight stages needed to pass the fourth power of the expansion
order. -/
noncomputable def lm311AdaptiveStages (n : ℕ) : ℕ :=
  Nat.log 8 (lmExpansionOrder n ^ 4) + 1

/-- Total number of local adaptive-growth rounds. -/
noncomputable def lm311AdaptiveRounds (n : ℕ) : ℕ :=
  lm311AdaptiveTime (lm311AdaptiveStages n)

/-- A cubic upper bound for the explicit adaptive clock. -/
theorem lm311AdaptiveTime_le (j : ℕ) :
    lm311AdaptiveTime j ≤ 917504 * j * (j + 2) ^ 2 := by
  induction j with
  | zero => simp [lm311AdaptiveTime]
  | succ j ih =>
      rw [lm311AdaptiveTime]
      calc
        lm311AdaptiveTime j + 14 * lm311AdaptiveBlock j
            ≤ 917504 * j * (j + 2) ^ 2 +
                14 * lm311AdaptiveBlock j := Nat.add_le_add_right ih _
        _ = 917504 * (j + 1) * (j + 2) ^ 2 := by
          simp [lm311AdaptiveBlock]
          ring
        _ ≤ 917504 * (j + 1) * (j + 3) ^ 2 := by
          gcongr <;> omega

/-- A fixed power of the logarithm is eventually at most the identity. -/
theorem eventually_log_pow_le_self (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ k ≤ x := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := k)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hxone
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hlogpow : 0 ≤ Real.log x ^ k := pow_nonneg hlog k
  simpa only [one_mul, id_eq, Real.norm_eq_abs, abs_of_nonneg hlogpow,
    abs_of_nonneg (zero_le_one.trans hxone)] using hx

/-- Coefficient-aware form of `eventually_log_pow_le_self`.  Keeping the
constant explicit is useful when a finite collection of carrier and contact
budgets is absorbed into a logarithmic growth scale. -/
theorem eventually_const_mul_log_pow_le_self (C : ℝ) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ k ≤ x := by
  by_cases hC : C ≤ 0
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    exact (mul_nonpos_of_nonpos_of_nonneg hC (pow_nonneg hlog k)).trans
      (zero_le_one.trans hx)
  · have hCpos : 0 < C := lt_of_not_ge hC
    have h := (Real.isLittleO_pow_log_id_atTop (n := k)).bound
      (inv_pos.mpr hCpos)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hxone
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hxone
    have hlogpow : 0 ≤ Real.log x ^ k := pow_nonneg hlog k
    have hx'' : Real.log x ^ k ≤ C⁻¹ * x := by
      simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hlogpow,
        abs_of_nonneg (zero_le_one.trans hxone)] using hx
    have hx' : Real.log x ^ k ≤ x / C := by
      simpa [div_eq_mul_inv, mul_comm] using hx''
    simpa [mul_comm] using (le_div_iff₀ hCpos).mp hx'

/-- Every fixed multiple of a fixed power of `log log n` is eventually at
most `log n`.  This is the basic comparison behind both the local Lemma 3.11
radius and its packing estimate. -/
theorem eventually_const_mul_log_log_pow_le_log (C : ℝ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      C * Real.log (Real.log (n : ℝ)) ^ k ≤ Real.log (n : ℝ) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact hlog.eventually (eventually_const_mul_log_pow_le_self C k)

/-- Ceiling-safe bounds for the local fifth-power iterated-logarithm
radius. -/
theorem lm311LocalRadius_bounds {n : ℕ}
    (hlarge : 1 ≤ 2 * Real.log (Real.log (n : ℝ)) ^ 5) :
    2 * Real.log (Real.log (n : ℝ)) ^ 5 ≤ (lm311LocalRadius n : ℝ) ∧
      (lm311LocalRadius n : ℝ) ≤
        4 * Real.log (Real.log (n : ℝ)) ^ 5 := by
  constructor
  · exact Nat.le_ceil _
  · have hceil : (lm311LocalRadius n : ℝ) <
        2 * Real.log (Real.log (n : ℝ)) ^ 5 + 1 := by
      apply Nat.ceil_lt_add_one
      positivity
    linarith

/-- The source local radius is eventually positive. -/
theorem eventually_lm311LocalRadius_pos :
    ∀ᶠ n : ℕ in atTop, 0 < lm311LocalRadius n := by
  have hloglog : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hloglog.eventually (eventually_gt_atTop (1 : ℝ))]
    with n hn
  exact Nat.ceil_pos.mpr
    (mul_pos (by norm_num) (pow_pos (zero_lt_one.trans hn) 5))

/-- The preliminary Lemma 3.11 radius is negligible compared with even one
power of `log n`.  The natural-ceiling formulation is convenient for radius
and packing arithmetic downstream. -/
theorem eventually_lm311LocalRadius_le_lmLogCubeCeil :
    ∀ᶠ n : ℕ in atTop, lm311LocalRadius n ≤ lmLogCubeCeil n := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards
      [eventually_const_mul_log_log_pow_le_log 4 5,
        hlog.eventually (eventually_ge_atTop (1 : ℝ)),
        hloglog.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hlocal hlogone hloglogone
  have hloglogpow : 1 ≤ Real.log (Real.log (n : ℝ)) ^ 5 :=
    one_le_pow₀ hloglogone
  have hlocalBounds := lm311LocalRadius_bounds
    (n := n) (by nlinarith)
  have htarget : (lm311LocalRadius n : ℝ) ≤
      (lmLogCubeCeil n : ℝ) := by
    calc
      (lm311LocalRadius n : ℝ)
          ≤ 4 * Real.log (Real.log (n : ℝ)) ^ 5 := hlocalBounds.2
      _ ≤ Real.log (n : ℝ) := hlocal
      _ ≤ Real.log (n : ℝ) ^ 3 := by nlinarith [sq_nonneg (Real.log (n : ℝ))]
      _ ≤ (lmLogCubeCeil n : ℝ) := Nat.le_ceil _
  exact_mod_cast htarget

/-- The base-two natural logarithm is bounded by twice the natural
logarithm.  This converts the Moore-cycle budget used by source Lemma 3.11
to the same real logarithmic scale as the other parameters. -/
theorem natLog_two_le_two_log {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  let k := Nat.log 2 n
  have hn0 : n ≠ 0 := by omega
  have hpowNat : 2 ^ k ≤ n := Nat.pow_log_le_self 2 hn0
  have hpowReal : (((2 ^ k : ℕ) : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast hpowNat
  have hlogPow : (k : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log
      (by positivity : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ)) hpowReal
    simpa [Real.log_pow] using h
  have hlogTwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  dsimp [k] at hlogPow ⊢
  nlinarith

/-- Dividing the identity by a fixed logarithmic power still tends to
infinity. -/
theorem tendsto_id_div_log_pow_atTop (k : ℕ) :
    Tendsto (fun x : ℝ ↦ x / Real.log x ^ k) atTop atTop := by
  have hzero :
      Tendsto (fun x : ℝ ↦ Real.log x ^ k / x) atTop (nhds 0) := by
    simpa only [one_mul, zero_add, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero)
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x ^ k / x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (pow_pos (Real.log_pos hx) k) (zero_lt_one.trans hx)
  have hright :
      Tendsto (fun x : ℝ ↦ Real.log x ^ k / x) atTop
        (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have hinv := hright.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Pi.inv_apply, inv_div]

/-- The lower endpoint guaranteed by the cycle-interval theorem tends to
infinity with the average degree. -/
theorem tendsto_lmOutputScale_atTop : Tendsto lmOutputScale atTop atTop := by
  refine (Tendsto.atTop_div_const (show (0 : ℝ) < 10 by norm_num)
    (tendsto_id_div_log_pow_atTop 12)).congr' (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [lmOutputScale]
  ring

/-- Threshold form of `tendsto_lmOutputScale_atTop`. -/
theorem eventually_lmOutputScale_ge (L : ℝ) :
    ∀ᶠ d : ℝ in atTop, L ≤ lmOutputScale d :=
  tendsto_lmOutputScale_atTop.eventually (eventually_ge_atTop L)

/-- Existential threshold form, convenient when assembling a single absolute
constant from several requirements. -/
theorem exists_lmOutputScale_threshold (L : ℝ) :
    ∃ D : ℝ, ∀ d : ℝ, D ≤ d → L ≤ lmOutputScale d := by
  simpa only [eventually_atTop] using eventually_lmOutputScale_ge L

/-- The unfloored exact-path endpoint tends to infinity. -/
theorem tendsto_lmPathScale_atTop : Tendsto lmPathScale atTop atTop := by
  apply (tendsto_id_div_log_pow_atTop 12).congr'
  exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- The natural floor of the exact-path endpoint also tends to infinity. -/
theorem tendsto_lmFloorEndpoint_atTop : Tendsto lmFloorEndpoint atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    (tendsto_lmPathScale_atTop.comp tendsto_natCast_atTop_atTop)

/-- Once `x ≥ 2`, taking the natural floor loses at most a factor of two. -/
lemma half_le_natFloor {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hfloor := Nat.lt_floor_add_one x
  norm_num at hfloor ⊢
  linarith

/-! ## Ceiling-safe adjuster radii -/

/-- The real simple-adjuster radius is at most its chosen natural ceiling. -/
theorem lmSimpleRadius_lower (ε₁ : ℝ) (n : ℕ) :
    (400 / ε₁) * Real.log (n : ℝ) ^ 3 ≤ (lmSimpleRadius ε₁ n : ℝ) := by
  exact Nat.le_ceil _

/-- Taking the simple radius ceiling loses less than one. -/
theorem lmSimpleRadius_lt_add_one {ε₁ : ℝ} {n : ℕ} (hε₁ : 0 < ε₁) :
    (lmSimpleRadius ε₁ n : ℝ) <
      (400 / ε₁) * Real.log (n : ℝ) ^ 3 + 1 := by
  apply Nat.ceil_lt_add_one
  exact mul_nonneg (by positivity) (by positivity)

/-- The real chained-adjuster radius is at most its natural ceiling. -/
theorem lmRadius_lower (ε₁ : ℝ) (n : ℕ) :
    (1600 / ε₁) * Real.log (n : ℝ) ^ 3 ≤ (lmRadius ε₁ n : ℝ) := by
  exact Nat.le_ceil _

/-- Taking the chained radius ceiling loses less than one. -/
theorem lmRadius_lt_add_one {ε₁ : ℝ} {n : ℕ} (hε₁ : 0 < ε₁) :
    (lmRadius ε₁ n : ℝ) <
      (1600 / ε₁) * Real.log (n : ℝ) ^ 3 + 1 := by
  apply Nat.ceil_lt_add_one
  exact mul_nonneg (by positivity) (by positivity)

/-- Once the underlying simple radius is at least one, doubling its ceiling
fits inside the ceiling chosen for the chained radius. -/
theorem two_mul_lmSimpleRadius_le_lmRadius {ε₁ : ℝ} {n : ℕ}
    (hε₁ : 0 < ε₁)
    (hlarge : 1 ≤ (400 / ε₁) * Real.log (n : ℝ) ^ 3) :
    2 * lmSimpleRadius ε₁ n ≤ lmRadius ε₁ n := by
  let x := (400 / ε₁) * Real.log (n : ℝ) ^ 3
  have hs : (lmSimpleRadius ε₁ n : ℝ) < x + 1 := by
    simpa [x] using lmSimpleRadius_lt_add_one (n := n) hε₁
  have hscale : (1600 / ε₁) * Real.log (n : ℝ) ^ 3 = 4 * x := by
    dsimp [x]
    ring
  have hr : 4 * x ≤ (lmRadius ε₁ n : ℝ) := by
    rw [← hscale]
    exact lmRadius_lower ε₁ n
  have hcast : ((2 * lmSimpleRadius ε₁ n : ℕ) : ℝ) ≤
      (lmRadius ε₁ n : ℝ) := by
    push_cast
    change 1 ≤ x at hlarge
    nlinarith
  exact_mod_cast hcast

/-- For fixed positive `ε₁`, the simple-adjuster radius tends to infinity. -/
theorem tendsto_lmSimpleRadius_atTop {ε₁ : ℝ} (hε₁ : 0 < ε₁) :
    Tendsto (lmSimpleRadius ε₁) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (show 3 ≠ 0 by norm_num)).comp hlog
  have hreal : Tendsto
      (fun n : ℕ ↦ (400 / ε₁) * Real.log (n : ℝ) ^ 3) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) hpow
  exact tendsto_nat_ceil_atTop.comp hreal

/-- Thus the doubling comparison needed when chaining simple adjusters holds
eventually. -/
theorem eventually_two_mul_lmSimpleRadius_le_lmRadius {ε₁ : ℝ}
    (hε₁ : 0 < ε₁) :
    ∀ᶠ n : ℕ in atTop, 2 * lmSimpleRadius ε₁ n ≤ lmRadius ε₁ n := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (show 3 ≠ 0 by norm_num)).comp hlog
  have hreal : Tendsto
      (fun n : ℕ ↦ (400 / ε₁) * Real.log (n : ℝ) ^ 3) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) hpow
  filter_upwards [hreal.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
  exact two_mul_lmSimpleRadius_le_lmRadius hε₁ hn

/-- The expansion order is no smaller than its real target. -/
theorem lmExpansionOrder_lower (n : ℕ) :
    Real.log (n : ℝ) ^ 10 ≤ (lmExpansionOrder n : ℝ) := by
  exact Nat.le_ceil _

/-- Its ceiling is bounded by twice the target as soon as that target is at
least one. -/
theorem lmExpansionOrder_le_two_mul {n : ℕ}
    (hlarge : 1 ≤ Real.log (n : ℝ) ^ 10) :
    (lmExpansionOrder n : ℝ) ≤ 2 * Real.log (n : ℝ) ^ 10 := by
  have hceil : (lmExpansionOrder n : ℝ) < Real.log (n : ℝ) ^ 10 + 1 := by
    apply Nat.ceil_lt_add_one
    positivity
  linarith

/-- The expansion order is positive once `n > 1`. -/
theorem lmExpansionOrder_pos {n : ℕ} (hn : 1 < n) :
    0 < lmExpansionOrder n := by
  have htarget : 0 < Real.log (n : ℝ) ^ 10 := by
    exact pow_pos (Real.log_pos (by exact_mod_cast hn)) 10
  have hcast : (0 : ℝ) < (lmExpansionOrder n : ℝ) :=
    htarget.trans_le (lmExpansionOrder_lower n)
  exact_mod_cast hcast

/-- The natural logarithmic cube is between its target and twice its target
once the target is at least one. -/
theorem lmLogCubeCeil_bounds {n : ℕ}
    (hlarge : 1 ≤ Real.log (n : ℝ) ^ 3) :
    Real.log (n : ℝ) ^ 3 ≤ (lmLogCubeCeil n : ℝ) ∧
      (lmLogCubeCeil n : ℝ) ≤ 2 * Real.log (n : ℝ) ^ 3 := by
  constructor
  · exact Nat.le_ceil _
  · have hceil : (lmLogCubeCeil n : ℝ) < Real.log (n : ℝ) ^ 3 + 1 := by
      apply Nat.ceil_lt_add_one
      positivity
    linarith

/-- The two star-carrier inequalities in the source Lemma 3.11 certificate
hold at the standard order and radius.  The first conjunct is the high-hub
budget; the second is the smaller low-reservoir budget. -/
theorem eventually_lm311_star_budgets :
    ∀ᶠ n : ℕ in atTop,
      let D := lmExpansionOrder n
      let R := lmRadius ((1 : ℝ) / 1024) n
      let girth := 2 * (Nat.log 2 n + 2)
      D + girth + 2 + 4 * (3 * R + 1) + 4 * D ≤ D ^ 2 ∧
        D + girth + 2 + 4 * D ≤ D ^ 2 := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [eventually_ge_atTop (1 : ℕ),
        hlog.eventually (eventually_ge_atTop (1 : ℝ)),
        hlog.eventually (eventually_ge_atTop (19660840 : ℝ))]
      with n hn hLone hLlarge
  let L := Real.log (n : ℝ)
  let D := lmExpansionOrder n
  let R := lmRadius ((1 : ℝ) / 1024) n
  let girth := 2 * (Nat.log 2 n + 2)
  have hDupper : (D : ℝ) ≤ 2 * L ^ 10 := by
    simpa [D, L] using lmExpansionOrder_le_two_mul
      (n := n) (one_le_pow₀ hLone)
  have hDlower : L ^ 10 ≤ (D : ℝ) := by
    simpa [D, L] using lmExpansionOrder_lower n
  have hRceil : (R : ℝ) < 1638400 * L ^ 3 + 1 := by
    convert
      (lmRadius_lt_add_one (n := n)
        (show (0 : ℝ) < 1 / 1024 by norm_num)) using 1 <;>
      norm_num [R, L]
  have hRupper : (R : ℝ) ≤ 1638401 * L ^ 3 := by
    have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hLone
    linarith
  have hgirth : (girth : ℝ) ≤ 4 * L + 4 := by
    dsimp [girth]
    push_cast
    have hk := natLog_two_le_two_log hn
    linarith
  have hcoeff : (19660840 : ℝ) ≤ L ^ 10 := by
    have hLpow : L ≤ L ^ 10 := by
      calc
        L ≤ L ^ 3 := by nlinarith [sq_nonneg L]
        _ ≤ L ^ 10 := pow_le_pow_right₀ hLone (by omega)
    exact hLlarge.trans hLpow
  have hcarrierReal :
      (D : ℝ) + girth + 2 + 4 * (3 * (R : ℝ) + 1) + 4 * D ≤
        L ^ 20 := by
    calc
      (D : ℝ) + girth + 2 + 4 * (3 * (R : ℝ) + 1) + 4 * D
          ≤ 10 * L ^ 10 + (4 * L + 4) + 2 +
              12 * (1638401 * L ^ 3) + 4 := by nlinarith
      _ ≤ 19660840 * L ^ 10 := by
        have hL3 : L ^ 3 ≤ L ^ 10 :=
          pow_le_pow_right₀ hLone (by omega)
        have hL : L ≤ L ^ 10 := by
          calc
            L ≤ L ^ 3 := by nlinarith [sq_nonneg L]
            _ ≤ L ^ 10 := hL3
        have hLpow : 1 ≤ L ^ 10 := one_le_pow₀ hLone
        nlinarith
      _ ≤ L ^ 10 * L ^ 10 := by nlinarith
      _ = L ^ 20 := by ring
  have hDsq : L ^ 20 ≤ (D : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((D : ℝ) - L ^ 10)]
  have hhighReal :
      ((D + girth + 2 + 4 * (3 * R + 1) + 4 * D : ℕ) : ℝ) ≤
        ((D ^ 2 : ℕ) : ℝ) := by
    push_cast
    exact hcarrierReal.trans hDsq
  have hhigh : D + girth + 2 + 4 * (3 * R + 1) + 4 * D ≤ D ^ 2 := by
    exact_mod_cast hhighReal
  have hlow : D + girth + 2 + 4 * D ≤ D ^ 2 := by
    calc
      D + girth + 2 + 4 * D
          ≤ (D + girth + 2 + 4 * D) + 4 * (3 * R + 1) :=
            Nat.le_add_right _ _
      _ = D + girth + 2 + 4 * (3 * R + 1) + 4 * D := by omega
      _ ≤ D ^ 2 := hhigh
  exact ⟨hhigh, hlow⟩

/-- The squared polylogarithmic reservoir order is eventually below half of
the ambient order, as required by the low-degree branch of Lemma 3.11. -/
theorem eventually_lmExpansionOrder_sq_le_half :
    ∀ᶠ n : ℕ in atTop, lmExpansionOrder n ^ 2 ≤ n / 2 + 1 := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsmall := hcast.eventually
    (eventually_const_mul_log_pow_le_self 8 20)
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  filter_upwards
      [hsmall, hlog.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hnsmall hlogone
  let L := Real.log (n : ℝ)
  let D := lmExpansionOrder n
  have hD : (D : ℝ) ≤ 2 * L ^ 10 := by
    simpa [D, L] using lmExpansionOrder_le_two_mul
      (n := n) (one_le_pow₀ hlogone)
  have hsquare : (D : ℝ) ^ 2 ≤ (2 * L ^ 10) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg D) hD 2
  have hnsmall' : 8 * L ^ 20 ≤ (n : ℝ) := by
    simpa [L] using hnsmall
  have htwiceReal :
      ((2 * D ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    calc
      2 * (D : ℝ) ^ 2 ≤ 2 * (2 * L ^ 10) ^ 2 := by gcongr
      _ = 8 * L ^ 20 := by ring
      _ ≤ (n : ℝ) := hnsmall'
  have htwiceNat : 2 * D ^ 2 ≤ n := by exact_mod_cast htwiceReal
  have hhalf : D ^ 2 ≤ n / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    simpa [mul_comm] using htwiceNat
  simpa [D] using hhalf.trans (Nat.le_add_right _ 1)

/-- The exact packing inequality used by the `k = 2`, empty-reserved-set
instance of source Lemma 3.11.  Its large power is still `n ^ o(1)`: after
taking logarithms its exponent is bounded by a fixed multiple of
`(log log n)^6`. -/
theorem eventually_lm311_packing :
    ∀ᶠ n : ℕ in atTop,
      let D := lmExpansionOrder n
      let Delta := D ^ 2
      let ell₀ := lm311LocalRadius n
      let girth := 2 * (Nat.log 2 n + 2)
      (4 + (2 + girth)) * (Delta + 1) ^ (10 * ell₀) <
        n - (8 + girth + 2) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hloglog : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards
      [eventually_ge_atTop (1 : ℕ),
        hlog.eventually (eventually_ge_atTop (2 : ℝ)),
        hloglog.eventually (eventually_ge_atTop (1 : ℝ)),
        eventually_const_mul_log_log_pow_le_log 1850 6]
      with n hn hLtwo hllone hsmall
  let L := Real.log (n : ℝ)
  let ll := Real.log L
  let D := lmExpansionOrder n
  let Delta := D ^ 2
  let ell₀ := lm311LocalRadius n
  let girth := 2 * (Nat.log 2 n + 2)
  let factor := 4 + (2 + girth)
  let base := Delta + 1
  let exponent := 10 * ell₀
  let tail := 8 + girth + 2
  have hLone : 1 ≤ L := hLtwo.trans' (by norm_num)
  have hll0 : 0 ≤ ll := zero_le_one.trans hllone
  have hD : (D : ℝ) ≤ 2 * L ^ 10 := by
    simpa [D, L] using lmExpansionOrder_le_two_mul
      (n := n) (one_le_pow₀ hLone)
  have hDsq : (D : ℝ) ^ 2 ≤ 4 * L ^ 20 := by
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg D) hD 2
    calc
      (D : ℝ) ^ 2 ≤ (2 * L ^ 10) ^ 2 := hpow
      _ = 4 * L ^ 20 := by ring
  have hL20 : 0 ≤ L ^ 20 := pow_nonneg (zero_le_one.trans hLone) 20
  have hbase : (base : ℝ) ≤ L ^ 23 := by
    have hbase0 : (base : ℝ) ≤ 5 * L ^ 20 := by
      dsimp [base, Delta]
      push_cast
      have hL20one : 1 ≤ L ^ 20 := one_le_pow₀ hLone
      nlinarith
    have hL3five : (5 : ℝ) ≤ L ^ 3 := by
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hLtwo 3
      norm_num at hp
      linarith
    calc
      (base : ℝ) ≤ 5 * L ^ 20 := hbase0
      _ ≤ L ^ 3 * L ^ 20 :=
        mul_le_mul_of_nonneg_right hL3five hL20
      _ = L ^ 23 := by ring
  have hbasePos : (0 : ℝ) < (base : ℝ) := by
    exact_mod_cast (by dsimp [base]; omega : 0 < base)
  have hlogBase : Real.log (base : ℝ) ≤ 23 * ll := by
    have h := Real.log_le_log hbasePos hbase
    calc
      Real.log (base : ℝ) ≤ Real.log (L ^ 23) := h
      _ = 23 * ll := by simp [ll, Real.log_pow]
  have hellBounds := lm311LocalRadius_bounds (n := n) (by
    have hll5 : 1 ≤ ll ^ 5 := one_le_pow₀ hllone
    change 1 ≤ 2 * ll ^ 5
    nlinarith)
  have hexponent : (exponent : ℝ) ≤ 40 * ll ^ 5 := by
    dsimp [exponent]
    push_cast
    change 10 * (ell₀ : ℝ) ≤ 40 * ll ^ 5
    have hlocal : (ell₀ : ℝ) ≤ 4 * ll ^ 5 := by
      simpa [ell₀, ll, L] using hellBounds.2
    nlinarith only [hlocal]
  have hgirth : (girth : ℝ) ≤ 4 * L + 4 := by
    dsimp [girth]
    push_cast
    have hk := natLog_two_le_two_log hn
    change (Nat.log 2 n : ℝ) ≤ 2 * L at hk
    linarith
  have hfactorBound : (factor : ℝ) ≤ L ^ 5 := by
    have hrough : (factor : ℝ) ≤ 14 * L := by
      dsimp [factor]
      push_cast
      nlinarith
    have hL4 : (14 : ℝ) ≤ L ^ 4 := by
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hLtwo 4
      norm_num at hp
      linarith
    calc
      (factor : ℝ) ≤ 14 * L := hrough
      _ ≤ L ^ 4 * L := mul_le_mul_of_nonneg_right hL4 (zero_le_one.trans hLone)
      _ = L ^ 5 := by ring
  have hfactorPos : (0 : ℝ) < (factor : ℝ) := by
    exact_mod_cast (by dsimp [factor]; omega : 0 < factor)
  have hlogFactor : Real.log (factor : ℝ) ≤ 5 * ll := by
    calc
      Real.log (factor : ℝ) ≤ Real.log (L ^ 5) :=
        Real.log_le_log hfactorPos hfactorBound
      _ = 5 * ll := by simp [ll, Real.log_pow]
  have htailBound : (tail : ℝ) ≤ L ^ 6 := by
    have hrough : (tail : ℝ) ≤ 18 * L := by
      dsimp [tail]
      push_cast
      nlinarith
    have hL5 : (18 : ℝ) ≤ L ^ 5 := by
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hLtwo 5
      norm_num at hp
      linarith
    calc
      (tail : ℝ) ≤ 18 * L := hrough
      _ ≤ L ^ 5 * L := mul_le_mul_of_nonneg_right hL5 (zero_le_one.trans hLone)
      _ = L ^ 6 := by ring
  have htailPos : (0 : ℝ) < (tail : ℝ) := by
    exact_mod_cast (by dsimp [tail]; omega : 0 < tail)
  have hlogTail : Real.log (tail : ℝ) ≤ 6 * ll := by
    calc
      Real.log (tail : ℝ) ≤ Real.log (L ^ 6) :=
        Real.log_le_log htailPos htailBound
      _ = 6 * ll := by simp [ll, Real.log_pow]
  have hll_le_six : ll ≤ ll ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hllone (by omega : 1 ≤ 6)
  have hsmall' : 1850 * ll ^ 6 ≤ L := by simpa [L, ll] using hsmall
  have hlogProduct :
      Real.log (((factor * base ^ exponent : ℕ) : ℝ)) ≤ L / 2 := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hfactorPos.ne' (pow_ne_zero _ hbasePos.ne'),
      Real.log_pow]
    calc
      Real.log (factor : ℝ) + (exponent : ℝ) * Real.log (base : ℝ)
          ≤ 5 * ll + (40 * ll ^ 5) * (23 * ll) := by gcongr
      _ ≤ 925 * ll ^ 6 := by
        have := mul_le_mul_of_nonneg_left hll_le_six (by norm_num : (0 : ℝ) ≤ 5)
        nlinarith [pow_nonneg hll0 5]
      _ ≤ L / 2 := by linarith
  have hlogTailHalf : Real.log (tail : ℝ) ≤ L / 2 := by
    calc
      Real.log (tail : ℝ) ≤ 6 * ll := hlogTail
      _ ≤ 925 * ll ^ 6 := by
        have := mul_le_mul_of_nonneg_left hll_le_six (by norm_num : (0 : ℝ) ≤ 6)
        nlinarith
      _ ≤ L / 2 := by linarith
  have hproductPos : (0 : ℝ) < ((factor * base ^ exponent : ℕ) : ℝ) := by
    positivity
  have hproductExp : ((factor * base ^ exponent : ℕ) : ℝ) ≤ Real.exp (L / 2) := by
    calc
      ((factor * base ^ exponent : ℕ) : ℝ)
          = Real.exp (Real.log ((factor * base ^ exponent : ℕ) : ℝ)) := by
              rw [Real.exp_log hproductPos]
      _ ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr hlogProduct
  have htailExp : (tail : ℝ) ≤ Real.exp (L / 2) := by
    calc
      (tail : ℝ) = Real.exp (Real.log (tail : ℝ)) := by rw [Real.exp_log htailPos]
      _ ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr hlogTailHalf
  have hexpTwo : 2 < Real.exp (L / 2) := by
    have htwo : (2 : ℝ) < Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
    exact htwo.trans_le (Real.exp_le_exp.mpr (by linarith))
  have hsumReal :
      ((factor * base ^ exponent : ℕ) : ℝ) + (tail : ℝ) < (n : ℝ) := by
    calc
      ((factor * base ^ exponent : ℕ) : ℝ) + (tail : ℝ)
          ≤ 2 * Real.exp (L / 2) := by linarith
      _ < Real.exp (L / 2) * Real.exp (L / 2) := by
        nlinarith [Real.exp_pos (L / 2)]
      _ = Real.exp L := by rw [← Real.exp_add]; congr 1 <;> ring
      _ = (n : ℝ) := by
        change Real.exp (Real.log (n : ℝ)) = (n : ℝ)
        rw [Real.exp_log]
        exact_mod_cast (show 0 < n by omega)
  have hsumNat : factor * base ^ exponent + tail < n := by
    exact_mod_cast hsumReal
  have hpacking : factor * base ^ exponent < n - tail :=
    Nat.lt_sub_of_add_lt hsumNat
  simpa [D, Delta, ell₀, girth, factor, base, exponent, tail] using hpacking

/-- The complete adaptive local clock fits inside the source
`2 * (log log n)^5` radius, including the initial radius-one bootstrap. -/
theorem eventually_lm311AdaptiveRounds_succ_le_localRadius :
    ∀ᶠ n : ℕ in atTop,
      lm311AdaptiveRounds n + 1 ≤ lm311LocalRadius n := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards
      [eventually_ge_atTop (2 : ℕ),
        hlog.eventually (eventually_ge_atTop (2 : ℝ)),
        hloglog.eventually (eventually_ge_atTop (91204485121 : ℝ))]
      with n hn hLtwo hlllarge
  let L := Real.log (n : ℝ)
  let ll := Real.log L
  let D := lmExpansionOrder n
  let target := D ^ 4
  let j := Nat.log 8 target
  let stages := j + 1
  have hLone : 1 ≤ L := hLtwo.trans' (by norm_num)
  have hllone : 1 ≤ ll := hlllarge.trans' (by norm_num)
  have hll0 : 0 ≤ ll := zero_le_one.trans hllone
  have hDpos : 0 < D := by
    exact lmExpansionOrder_pos (by omega : 1 < n)
  have htargetPos : 0 < target := by
    dsimp [target]
    positivity
  have hpowNat : 8 ^ j ≤ target := by
    exact Nat.pow_log_le_self 8 htargetPos.ne'
  have hpowReal : (((8 ^ j : ℕ) : ℝ)) ≤ (target : ℝ) := by
    exact_mod_cast hpowNat
  have hlogPow : (j : ℝ) * Real.log 8 ≤ Real.log (target : ℝ) := by
    have h := Real.log_le_log
      (by positivity : (0 : ℝ) < ((8 ^ j : ℕ) : ℝ)) hpowReal
    simpa [Real.log_pow] using h
  have hlogEight : (1 : ℝ) ≤ Real.log 8 := by
    have heq : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    rw [heq]
    nlinarith [Real.log_two_gt_d9]
  have hjLog : (j : ℝ) ≤ Real.log (target : ℝ) := by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hD : (D : ℝ) ≤ 2 * L ^ 10 := by
    simpa [D, L] using lmExpansionOrder_le_two_mul
      (n := n) (one_le_pow₀ hLone)
  have hDpow : (target : ℝ) ≤ 16 * L ^ 40 := by
    dsimp [target]
    push_cast
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg D) hD 4
    calc
      (D : ℝ) ^ 4 ≤ (2 * L ^ 10) ^ 4 := hpow
      _ = 16 * L ^ 40 := by ring
  have htargetL : (target : ℝ) ≤ L ^ 44 := by
    have hL40 : 0 ≤ L ^ 40 := pow_nonneg (zero_le_one.trans hLone) 40
    have hL4sixteen : (16 : ℝ) ≤ L ^ 4 := by
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hLtwo 4
      norm_num at hp
      exact hp
    calc
      (target : ℝ) ≤ 16 * L ^ 40 := hDpow
      _ ≤ L ^ 4 * L ^ 40 :=
        mul_le_mul_of_nonneg_right hL4sixteen hL40
      _ = L ^ 44 := by ring
  have hlogTarget : Real.log (target : ℝ) ≤ 44 * ll := by
    calc
      Real.log (target : ℝ) ≤ Real.log (L ^ 44) :=
        Real.log_le_log (by positivity) htargetL
      _ = 44 * ll := by simp [ll, Real.log_pow]
  have hj : (j : ℝ) ≤ 44 * ll := hjLog.trans hlogTarget
  have hstages : (stages : ℝ) ≤ 45 * ll := by
    dsimp [stages]
    push_cast
    nlinarith
  have htimeNat := lm311AdaptiveTime_le stages
  have htime : (lm311AdaptiveTime stages : ℝ) ≤
      917504 * (stages : ℝ) * ((stages : ℝ) + 2) ^ 2 := by
    exact_mod_cast htimeNat
  have hstagesTwo : (stages : ℝ) + 2 ≤ 47 * ll := by
    calc
      (stages : ℝ) + 2 ≤ 45 * ll + 2 := by
        simpa [add_comm] using add_le_add_right hstages 2
      _ ≤ 47 * ll := by linarith
  have hrounds : (lm311AdaptiveRounds n : ℝ) ≤
      91204485120 * ll ^ 3 := by
    have hroundsEq : lm311AdaptiveRounds n = lm311AdaptiveTime stages := rfl
    rw [hroundsEq]
    calc
      (lm311AdaptiveTime stages : ℝ)
          ≤ 917504 * (stages : ℝ) * ((stages : ℝ) + 2) ^ 2 := htime
      _ ≤ 917504 * (45 * ll) * (47 * ll) ^ 2 := by gcongr
      _ = 91204485120 * ll ^ 3 := by ring
  have hll3one : 1 ≤ ll ^ 3 := one_le_pow₀ hllone
  have hcoeff : (91204485121 : ℝ) ≤ 2 * ll ^ 2 := by
    have hllsq : ll ≤ ll ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hllone hll0
      simpa [pow_two] using h
    calc
      (91204485121 : ℝ) ≤ ll := hlllarge
      _ ≤ ll ^ 2 := hllsq
      _ ≤ 2 * ll ^ 2 := by nlinarith only [sq_nonneg ll]
  have hroundsLocal : (lm311AdaptiveRounds n : ℝ) + 1 ≤ 2 * ll ^ 5 := by
    calc
      (lm311AdaptiveRounds n : ℝ) + 1
          ≤ 91204485120 * ll ^ 3 + 1 := by linarith
      _ ≤ 91204485120 * ll ^ 3 + ll ^ 3 := by
        linarith only [hll3one]
      _ = 91204485121 * ll ^ 3 := by ring
      _ ≤ (2 * ll ^ 2) * ll ^ 3 :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hll0 3)
      _ = 2 * ll ^ 5 := by ring
  have hlower : 2 * ll ^ 5 ≤ (lm311LocalRadius n : ℝ) := by
    simpa [ll, L] using (lm311LocalRadius_bounds (n := n) (by
      have hll5 : 1 ≤ ll ^ 5 := one_le_pow₀ hllone
      change 1 ≤ 2 * ll ^ 5
      exact hll5.trans (by nlinarith only [pow_nonneg hll0 5]))).1
  have hcast : ((lm311AdaptiveRounds n + 1 : ℕ) : ℝ) ≤
      (lm311LocalRadius n : ℝ) := by
    push_cast
    exact hroundsLocal.trans hlower
  exact_mod_cast hcast

/-- The product of the protected-expansion order and an adjuster radius fits
below the fixed fourteenth logarithmic power once `n` is sufficiently large.
This is the ceiling-safe estimate used when Lemma 4.3 is applied with the
inflated order `D * m` inside the adjuster-chain construction. -/
theorem lmExpansionOrder_mul_lmRadius_le_ceil_log14 {ε₁ : ℝ} {n : ℕ}
    (hε₁ : 0 < ε₁)
    (hlog_one : 1 ≤ Real.log (n : ℝ))
    (hlog_large :
      2 * (1600 / ε₁ + 1) ≤ Real.log (n : ℝ)) :
    lmExpansionOrder n * lmRadius ε₁ n ≤
      ⌈Real.log (n : ℝ) ^ 14⌉₊ := by
  let L := Real.log (n : ℝ)
  let c := 1600 / ε₁
  change 1 ≤ L at hlog_one
  change 2 * (c + 1) ≤ L at hlog_large
  have hD : (lmExpansionOrder n : ℝ) ≤ 2 * L ^ 10 := by
    simpa [L] using lmExpansionOrder_le_two_mul
      (n := n) (one_le_pow₀ hlog_one)
  have hrceil : (lmRadius ε₁ n : ℝ) < c * L ^ 3 + 1 := by
    simpa [c, L] using lmRadius_lt_add_one (n := n) hε₁
  have hL3one : 1 ≤ L ^ 3 := one_le_pow₀ hlog_one
  have hr : (lmRadius ε₁ n : ℝ) ≤ (c + 1) * L ^ 3 := by
    nlinarith
  have hprod₀ :
      (lmExpansionOrder n : ℝ) * (lmRadius ε₁ n : ℝ) ≤
        (2 * L ^ 10) * ((c + 1) * L ^ 3) := by
    exact mul_le_mul hD hr (by positivity) (by positivity)
  have hcoeff : 2 * (c + 1) * L ^ 13 ≤ L ^ 14 := by
    have h := mul_le_mul_of_nonneg_right hlog_large
      (pow_nonneg (zero_le_one.trans hlog_one) 13)
    nlinarith
  have hceil : L ^ 14 ≤ (⌈Real.log (n : ℝ) ^ 14⌉₊ : ℝ) := by
    change L ^ 14 ≤ (⌈L ^ 14⌉₊ : ℝ)
    exact Nat.le_ceil _
  have hcast :
      ((lmExpansionOrder n * lmRadius ε₁ n : ℕ) : ℝ) ≤
        (⌈Real.log (n : ℝ) ^ 14⌉₊ : ℝ) := by
    push_cast
    calc
      (lmExpansionOrder n : ℝ) * (lmRadius ε₁ n : ℝ) ≤
          (2 * L ^ 10) * ((c + 1) * L ^ 3) := hprod₀
      _ = 2 * (c + 1) * L ^ 13 := by ring
      _ ≤ L ^ 14 := hcoeff
      _ ≤ (⌈Real.log (n : ℝ) ^ 14⌉₊ : ℝ) := hceil
  exact_mod_cast hcast

/-- Eventual form of the inflated-order estimate, uniform for every fixed
positive `ε₁`. -/
theorem eventually_lmExpansionOrder_mul_lmRadius_le_ceil_log14
    {ε₁ : ℝ} (hε₁ : 0 < ε₁) :
    ∀ᶠ n : ℕ in atTop,
      lmExpansionOrder n * lmRadius ε₁ n ≤
        ⌈Real.log (n : ℝ) ^ 14⌉₊ := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hone := hlog.eventually (eventually_ge_atTop (1 : ℝ))
  have hlarge := hlog.eventually
    (eventually_ge_atTop (2 * (1600 / ε₁ + 1)))
  filter_upwards [hone, hlarge] with n hn hnlarge
  exact lmExpansionOrder_mul_lmRadius_le_ceil_log14 hε₁ hn hnlarge

/-- The exact specialization used by the unconditional Lemma 4.7 parameter
choice. -/
theorem eventually_lmExpansionOrder_mul_lmRadius_1024_le_ceil_log14 :
    ∀ᶠ n : ℕ in atTop,
      lmExpansionOrder n * lmRadius ((1 : ℝ) / 1024) n ≤
        ⌈Real.log (n : ℝ) ^ 14⌉₊ := by
  exact eventually_lmExpansionOrder_mul_lmRadius_le_ceil_log14
    (show (0 : ℝ) < 1 / 1024 by norm_num)

/-- A pointwise polynomial estimate showing that the entire adjuster core
fits below the lower exact-path scale. -/
theorem adjuster_core_le_ceil_log_seven {ε₁ : ℝ} {n : ℕ}
    (hε₁ : 0 < ε₁)
    (hlog_one : 1 ≤ Real.log (n : ℝ))
    (hlog_large :
      220 * (1600 / ε₁ + 1) ^ 2 + 22 * (1600 / ε₁ + 1) + 1 ≤
        Real.log (n : ℝ)) :
    220 * lmRadius ε₁ n ^ 2 + 22 * lmRadius ε₁ n + 1 ≤
      ⌈Real.log (n : ℝ) ^ 7⌉₊ := by
  let L := Real.log (n : ℝ)
  let c := 1600 / ε₁
  let A := (c + 1) * L ^ 3
  let C := 220 * (c + 1) ^ 2 + 22 * (c + 1) + 1
  change 1 ≤ L at hlog_one
  change C ≤ L at hlog_large
  have hc : 0 < c := by dsimp [c]; positivity
  have hL3one : 1 ≤ L ^ 3 := one_le_pow₀ hlog_one
  have hrceil : (lmRadius ε₁ n : ℝ) < c * L ^ 3 + 1 := by
    simpa [c, L] using lmRadius_lt_add_one (n := n) hε₁
  have hrA : (lmRadius ε₁ n : ℝ) ≤ A := by
    dsimp [A]
    nlinarith
  have hrA2 : (lmRadius ε₁ n : ℝ) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (by positivity) hrA 2
  have hL3L6 : L ^ 3 ≤ L ^ 6 :=
    pow_le_pow_right₀ hlog_one (by norm_num)
  have hL6one : 1 ≤ L ^ 6 := one_le_pow₀ hlog_one
  have hAlinear : A ≤ (c + 1) * L ^ 6 := by
    dsimp [A]
    exact mul_le_mul_of_nonneg_left hL3L6 (by positivity)
  have hA2eq : A ^ 2 = (c + 1) ^ 2 * L ^ 6 := by
    dsimp [A]
    ring
  have hpoly :
      220 * (lmRadius ε₁ n : ℝ) ^ 2 +
          22 * (lmRadius ε₁ n : ℝ) + 1 ≤ C * L ^ 6 := by
    dsimp [C]
    nlinarith [hA2eq, pow_nonneg (by positivity : 0 ≤ c + 1) 2,
      pow_nonneg (zero_le_one.trans hlog_one) 3]
  have hCL : C * L ^ 6 ≤ L ^ 7 := by
    have := mul_le_mul_of_nonneg_right hlog_large
      (pow_nonneg (zero_le_one.trans hlog_one) 6)
    nlinarith
  have hceil : L ^ 7 ≤ (⌈Real.log (n : ℝ) ^ 7⌉₊ : ℝ) := by
    change L ^ 7 ≤ (⌈L ^ 7⌉₊ : ℝ)
    exact Nat.le_ceil _
  have hcast :
      ((220 * lmRadius ε₁ n ^ 2 + 22 * lmRadius ε₁ n + 1 : ℕ) : ℝ) ≤
        (⌈Real.log (n : ℝ) ^ 7⌉₊ : ℝ) := by
    push_cast
    exact hpoly.trans (hCL.trans hceil)
  exact_mod_cast hcast

/-- Eventual form of the adjuster-core estimate. -/
theorem eventually_adjuster_core_le_ceil_log_seven {ε₁ : ℝ}
    (hε₁ : 0 < ε₁) :
    ∀ᶠ n : ℕ in atTop,
      220 * lmRadius ε₁ n ^ 2 + 22 * lmRadius ε₁ n + 1 ≤
        ⌈Real.log (n : ℝ) ^ 7⌉₊ := by
  let C : ℝ :=
    220 * (1600 / ε₁ + 1) ^ 2 + 22 * (1600 / ε₁ + 1) + 1
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hone := hlog.eventually (eventually_ge_atTop (1 : ℝ))
  have hC := hlog.eventually (eventually_ge_atTop C)
  filter_upwards [hone, hC] with n hn hCn
  exact adjuster_core_le_ceil_log_seven hε₁ hn hCn

/-- Real-valued form of the core-versus-expansion inequality.  It is often
the most convenient version before cardinalities are rounded to naturals. -/
theorem eventually_core_le_expansionOrder_div_logCube {ε₁ : ℝ}
    (hε₁ : 0 < ε₁) :
    ∀ᶠ n : ℕ in atTop,
      (500 * lmRadius ε₁ n ^ 2 : ℕ) ≤
        (lmExpansionOrder n : ℝ) / (2 * Real.log (n : ℝ) ^ 3) := by
  let c := 1600 / ε₁
  let K := 1000 * (c + 1) ^ 2
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hone := hlog.eventually (eventually_ge_atTop (1 : ℝ))
  have hK := hlog.eventually (eventually_ge_atTop K)
  filter_upwards [hone, hK] with n hn hKn
  let L := Real.log (n : ℝ)
  let A := (c + 1) * L ^ 3
  change 1 ≤ L at hn
  change K ≤ L at hKn
  have hrceil : (lmRadius ε₁ n : ℝ) < c * L ^ 3 + 1 := by
    simpa [c, L] using lmRadius_lt_add_one (n := n) hε₁
  have hrA : (lmRadius ε₁ n : ℝ) ≤ A := by
    dsimp [A]
    have hL3one : 1 ≤ L ^ 3 := one_le_pow₀ hn
    nlinarith
  have hrA2 : (lmRadius ε₁ n : ℝ) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (by positivity) hrA 2
  have hrA2L3 :
      (lmRadius ε₁ n : ℝ) ^ 2 * L ^ 3 ≤ A ^ 2 * L ^ 3 :=
      mul_le_mul_of_nonneg_right hrA2 (pow_nonneg (zero_le_one.trans hn) 3)
  have htarget :
      (500 * lmRadius ε₁ n ^ 2 : ℕ) ≤ L ^ 10 / (2 * L ^ 3) := by
    push_cast
    rw [le_div_iff₀ (by positivity : 0 < 2 * L ^ 3)]
    dsimp [A, K] at hrA2L3 hKn ⊢
    nlinarith [pow_nonneg (by positivity : 0 ≤ c + 1) 2,
      pow_nonneg (zero_le_one.trans hn) 6,
      mul_le_mul_of_nonneg_right hKn (pow_nonneg (zero_le_one.trans hn) 9)]
  calc
    ((500 * lmRadius ε₁ n ^ 2 : ℕ) : ℝ) ≤
        L ^ 10 / (2 * L ^ 3) := htarget
    _ ≤ (lmExpansionOrder n : ℝ) / (2 * L ^ 3) := by
      exact div_le_div_of_nonneg_right (lmExpansionOrder_lower n) (by positivity)

/-- A fully natural conservative version of the preceding estimate. -/
theorem eventually_core_le_expansionOrder_div_logCubeCeil {ε₁ : ℝ}
    (hε₁ : 0 < ε₁) :
    ∀ᶠ n : ℕ in atTop,
      500 * lmRadius ε₁ n ^ 2 ≤
        lmExpansionOrder n / (2 * lmLogCubeCeil n) := by
  let c := 1600 / ε₁
  let K := 2000 * (c + 1) ^ 2
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hone := hlog.eventually (eventually_ge_atTop (1 : ℝ))
  have hK := hlog.eventually (eventually_ge_atTop K)
  filter_upwards [hone, hK] with n hn hKn
  let L := Real.log (n : ℝ)
  let A := (c + 1) * L ^ 3
  change 1 ≤ L at hn
  change K ≤ L at hKn
  have hcube := lmLogCubeCeil_bounds (n := n) (one_le_pow₀ hn)
  have hcube_pos : 0 < lmLogCubeCeil n := by
    have hL3pos : 0 < L ^ 3 := by positivity
    have hlow : L ^ 3 ≤ (lmLogCubeCeil n : ℝ) := by
      simpa [L] using hcube.1
    have hcast : (0 : ℝ) < (lmLogCubeCeil n : ℝ) := by
      exact hL3pos.trans_le hlow
    exact_mod_cast hcast
  have hrceil : (lmRadius ε₁ n : ℝ) < c * L ^ 3 + 1 := by
    simpa [c, L] using lmRadius_lt_add_one (n := n) hε₁
  have hrA : (lmRadius ε₁ n : ℝ) ≤ A := by
    dsimp [A]
    have hL3one : 1 ≤ L ^ 3 := one_le_pow₀ hn
    nlinarith
  have hrA2 : (lmRadius ε₁ n : ℝ) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (by positivity) hrA 2
  have hprod :
      (lmRadius ε₁ n : ℝ) ^ 2 * (lmLogCubeCeil n : ℝ) ≤
        A ^ 2 * (2 * L ^ 3) := by
    exact mul_le_mul hrA2 hcube.2 (by positivity) (by positivity)
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * lmLogCubeCeil n)).2
  have hcast :
      (((500 * lmRadius ε₁ n ^ 2) * (2 * lmLogCubeCeil n) : ℕ) : ℝ) ≤
        (lmExpansionOrder n : ℝ) := by
    push_cast
    apply le_trans ?_ (lmExpansionOrder_lower n)
    dsimp [A, K] at hprod hKn ⊢
    nlinarith [pow_nonneg (by positivity : 0 ≤ c + 1) 2,
      pow_nonneg (zero_le_one.trans hn) 9,
      mul_le_mul_of_nonneg_right hKn (pow_nonneg (zero_le_one.trans hn) 9)]
  exact_mod_cast hcast

/-- The floor endpoint never exceeds the unfloored path scale. -/
theorem lmFloorEndpoint_le_pathScale (n : ℕ)
    (hscale : 0 ≤ lmPathScale (n : ℝ)) :
    (lmFloorEndpoint n : ℝ) ≤ lmPathScale (n : ℝ) := by
  exact Nat.floor_le hscale

/-! ## Restoring the floor in the exact-path window -/

/-- The logarithmic denominator in `lmPathScale` is eventually at most the
square root.  Squaring reduces this to the standard estimate
`(log x)^24 ≤ x`. -/
theorem eventually_log_pow_twelve_le_sqrt :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 12 ≤ √x := by
  filter_upwards [eventually_log_pow_le_self 24] with x hx
  apply Real.le_sqrt_of_sq_le
  calc
    (Real.log x ^ 12) ^ 2 = Real.log x ^ 24 := by ring
    _ ≤ x := hx

/-- A pointwise version of the comparison between the exact-path scale and
the square root. -/
lemma sqrt_le_lmPathScale {x : ℝ} (hx : 1 < x)
    (hlog : Real.log x ^ 12 ≤ √x) :
    √x ≤ lmPathScale x := by
  have hden : 0 < Real.log x ^ 12 := pow_pos (Real.log_pos hx) 12
  rw [lmPathScale, le_div_iff₀ hden]
  calc
    √x * Real.log x ^ 12 ≤ √x * √x :=
      mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)
    _ = x := Real.mul_self_sqrt (zero_lt_one.trans hx).le

/-- For large natural `n`, the logarithm of the floored path endpoint is at
least one quarter of `log n`.  The deliberately generous factor `1/4`
absorbs both the twelve logarithmic factors and the floor. -/
lemma quarter_log_le_log_lmFloorEndpoint {n : ℕ} (hn : 256 ≤ n)
    (hlog : Real.log (n : ℝ) ^ 12 ≤ √(n : ℝ)) :
    Real.log (n : ℝ) / 4 ≤ Real.log (lmFloorEndpoint n : ℝ) := by
  have hnreal : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hn16 : (16 : ℝ) ≤ n := by linarith
  have hnone : (1 : ℝ) < n := by linarith
  have hsqrt16 : (16 : ℝ) ≤ √(n : ℝ) := by
    calc
      (16 : ℝ) = √(256 : ℝ) := by norm_num
      _ ≤ √(n : ℝ) := Real.sqrt_le_sqrt hnreal
  have hpath : √(n : ℝ) ≤ lmPathScale (n : ℝ) :=
    sqrt_le_lmPathScale hnone hlog
  have hpath_two : (2 : ℝ) ≤ lmPathScale (n : ℝ) :=
    (by linarith : (2 : ℝ) ≤ √(n : ℝ)).trans hpath
  have hfloor : √(n : ℝ) / 2 ≤ (lmFloorEndpoint n : ℝ) := by
    calc
      √(n : ℝ) / 2 ≤ lmPathScale (n : ℝ) / 2 := by gcongr
      _ ≤ (lmFloorEndpoint n : ℝ) := by
        exact half_le_natFloor hpath_two
  have hsqrt_pos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hlog_floor :
      Real.log (√(n : ℝ) / 2) ≤ Real.log (lmFloorEndpoint n : ℝ) :=
    Real.log_le_log (div_pos hsqrt_pos (by norm_num)) hfloor
  have hlog16 : Real.log (16 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hn16
  have hfourlog : 4 * Real.log 2 ≤ Real.log (n : ℝ) := by
    simpa [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] using hlog16
  calc
    Real.log (n : ℝ) / 4 ≤ Real.log (n : ℝ) / 2 - Real.log 2 := by
      linarith
    _ = Real.log (√(n : ℝ) / 2) := by
      rw [Real.log_div hsqrt_pos.ne' (by norm_num : (2 : ℝ) ≠ 0),
        Real.log_sqrt (by positivity)]
    _ ≤ Real.log (lmFloorEndpoint n : ℝ) := hlog_floor

/-- Eventual form of `quarter_log_le_log_lmFloorEndpoint`. -/
theorem eventually_quarter_log_le_log_lmFloorEndpoint :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) / 4 ≤ Real.log (lmFloorEndpoint n : ℝ) := by
  have hlog := tendsto_natCast_atTop_atTop.eventually
    eventually_log_pow_twelve_le_sqrt
  filter_upwards [eventually_ge_atTop 256, hlog] with n hn hnlog
  exact quarter_log_le_log_lmFloorEndpoint hn hnlog

/-- The lower endpoint `(log ell)^8` of the final cycle interval is eventually
at least one more than the lower endpoint `(log n)^7` of the path interval,
even when `ell` is the natural floor of `n/(log n)^12`.  The extra `1` is the
edge used to close the path. -/
theorem eventually_path_lower_window :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ^ 7 + 1 ≤ Real.log (lmFloorEndpoint n : ℝ) ^ 8 := by
  have hlogtop :
      Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hlogtop.eventually
    (eventually_ge_atTop (2 * (4 : ℝ) ^ 8))
  filter_upwards [eventually_quarter_log_le_log_lmFloorEndpoint, hlarge]
    with n hquarter hnlog
  let a := Real.log (n : ℝ)
  let b := Real.log (lmFloorEndpoint n : ℝ)
  change a / 4 ≤ b at hquarter
  change 2 * (4 : ℝ) ^ 8 ≤ a at hnlog
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact Real.log_natCast_nonneg n
  have ha_one : 1 ≤ a := by
    dsimp [a] at hnlog ⊢
    norm_num at hnlog ⊢
    linarith
  have hpow : (a / 4) ^ 8 ≤ b ^ 8 := by
    exact pow_le_pow_left₀ (by positivity) hquarter 8
  have hone : 1 ≤ a ^ 7 := one_le_pow₀ ha_one
  have hmul : 2 * (4 : ℝ) ^ 8 * a ^ 7 ≤ a ^ 8 := by
    have := mul_le_mul_of_nonneg_right hnlog (pow_nonneg ha_nonneg 7)
    nlinarith
  have htwo : 2 * a ^ 7 ≤ (a / 4) ^ 8 := by
    rw [div_pow]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 ^ 8)).2
    nlinarith
  change a ^ 7 + 1 ≤ b ^ 8
  exact (by linarith : a ^ 7 + 1 ≤ 2 * a ^ 7) |>.trans (htwo.trans hpow)

/-- All floor-sensitive inequalities used to pass from a requested cycle
length to the exact-path theorem hold simultaneously for large `n`. -/
theorem eventually_lmFloorEndpoint_window :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ^ 7 + 1 ≤ Real.log (lmFloorEndpoint n : ℝ) ^ 8 ∧
      (lmFloorEndpoint n : ℝ) ≤ lmPathScale (n : ℝ) := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ lmPathScale (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_nonneg (by positivity) (by positivity)
  filter_upwards [eventually_path_lower_window, hpos] with n hlower hscale
  exact ⟨hlower, lmFloorEndpoint_le_pathScale n hscale⟩

/-- Pointwise application of the preceding window.  If an integer `m` lies
in the final cycle interval, then `m - 1` lies in the exact-path interval. -/
theorem sub_one_mem_path_window {n m : ℕ}
    (hwindow :
      Real.log (n : ℝ) ^ 7 + 1 ≤ Real.log (lmFloorEndpoint n : ℝ) ^ 8 ∧
      (lmFloorEndpoint n : ℝ) ≤ lmPathScale (n : ℝ))
    (hlower : Real.log (lmFloorEndpoint n : ℝ) ^ 8 ≤ (m : ℝ))
    (hupper : m ≤ lmFloorEndpoint n) :
    Real.log (n : ℝ) ^ 7 ≤ (m - 1 : ℕ) ∧
      (m - 1 : ℕ) ≤ lmPathScale (n : ℝ) := by
  have hmreal : Real.log (n : ℝ) ^ 7 + 1 ≤ (m : ℝ) :=
    hwindow.1.trans hlower
  have hmone : 1 ≤ m := by
    have hnonneg : 0 ≤ Real.log (n : ℝ) ^ 7 := by positivity
    exact_mod_cast (show (1 : ℝ) ≤ m by linarith)
  constructor
  · rw [Nat.cast_sub hmone]
    norm_num
    linarith
  · calc
      ((m - 1 : ℕ) : ℝ) ≤ (lmFloorEndpoint n : ℝ) := by
        exact_mod_cast (Nat.sub_le m 1).trans hupper
      _ ≤ lmPathScale (n : ℝ) := hwindow.2

/-! ## The final scale comparisons -/

/-- Replacing `d` by `d/8` in the expander reduction still leaves at least
the advertised Liu--Montgomery output scale.  The constant `10` has enough
slack to absorb the factor `8`. -/
theorem lmOutputScale_le_eighth_pathScale {d : ℝ} (hd : 8 < d) :
    lmOutputScale d ≤ lmPathScale (d / 8) := by
  have hd_pos : 0 < d := by linarith
  have heighth_pos : 1 < d / 8 := by linarith
  have hlogd_pos : 0 < Real.log d := Real.log_pos (by linarith)
  have hlogeighth_pos : 0 < Real.log (d / 8) := Real.log_pos heighth_pos
  have hlog : Real.log (d / 8) ≤ Real.log d := by
    apply Real.log_le_log (by positivity)
    linarith
  have hpow : Real.log (d / 8) ^ 12 ≤ Real.log d ^ 12 :=
    pow_le_pow_left₀ hlogeighth_pos.le hlog 12
  have hden : 8 * Real.log (d / 8) ^ 12 ≤ 10 * Real.log d ^ 12 := by
    have := mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ 8 by norm_num)
    nlinarith [pow_pos hlogd_pos 12]
  rw [lmOutputScale, lmPathScale]
  rw [show d / 8 / Real.log (d / 8) ^ 12 =
      d / (8 * Real.log (d / 8) ^ 12) by ring]
  exact div_le_div_of_nonneg_left hd_pos.le (by positivity) hden

/-- Eventual form of the preceding scale comparison. -/
theorem eventually_lmOutputScale_le_eighth_pathScale :
    ∀ᶠ d : ℝ in atTop, lmOutputScale d ≤ lmPathScale (d / 8) := by
  filter_upwards [eventually_gt_atTop (8 : ℝ)] with d hd
  exact lmOutputScale_le_eighth_pathScale hd

/-- In the subdivision branch, the natural choice `t = d / 16` still gives
an endpoint `2*t` above the theorem's output scale.  This statement includes
the full loss from natural-number division. -/
lemma lmOutputScale_le_twice_div_sixteen {d : ℕ} (hd : 80 ≤ d)
    (hlog : 1 ≤ Real.log (d : ℝ)) :
    lmOutputScale (d : ℝ) ≤ (2 * (d / 16) : ℕ) := by
  have hdreal : (80 : ℝ) ≤ d := by exact_mod_cast hd
  have hlogpow : (1 : ℝ) ≤ Real.log (d : ℝ) ^ 12 := one_le_pow₀ hlog
  have hfirst : lmOutputScale (d : ℝ) ≤ (d : ℝ) / 10 := by
    rw [lmOutputScale]
    apply div_le_div_of_nonneg_left (by positivity)
      (show (0 : ℝ) < 10 by norm_num)
    nlinarith
  have hround_nat : d ≤ 16 * (d / 16) + 15 := by omega
  have hround : (d : ℝ) / 8 - 2 ≤ (2 * (d / 16) : ℕ) := by
    have hround_real : (d : ℝ) ≤ 16 * (d / 16 : ℕ) + 15 := by
      exact_mod_cast hround_nat
    push_cast at hround_real ⊢
    linarith
  calc
    lmOutputScale (d : ℝ) ≤ (d : ℝ) / 10 := hfirst
    _ ≤ (d : ℝ) / 8 - 2 := by linarith
    _ ≤ (2 * (d / 16) : ℕ) := hround

/-- Eventual floor-safe subdivision endpoint comparison. -/
theorem eventually_lmOutputScale_le_twice_div_sixteen :
    ∀ᶠ d : ℕ in atTop,
      lmOutputScale (d : ℝ) ≤ (2 * (d / 16) : ℕ) := by
  have hlogtop : Tendsto (fun d : ℕ ↦ Real.log (d : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog := hlogtop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_ge_atTop 80, hlog] with d hd hdlog
  exact lmOutputScale_le_twice_div_sixteen hd hdlog

/-! ## Admissibility of a dyadic tail -/

/-- The growth inequality imposed on a term of the sequence in
Liu--Montgomery Corollary 1.3. -/
def DyadicGrowthAdmissible (m : ℕ) : Prop :=
  ((2 ^ (m + 1) : ℕ) : ℝ) ≤
    Real.exp (((2 ^ m : ℕ) : ℝ) ^ ((1 : ℝ) / 10))

/-- After taking logarithms, the dyadic growth condition follows from the
fact that an exponential eventually dominates a linear function. -/
theorem eventually_dyadic_log_growth :
    ∀ᶠ m : ℕ in atTop,
      ((m + 1 : ℕ) : ℝ) * Real.log 2 ≤
        Real.exp (((m : ℝ) * Real.log 2) / 10) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlarge : ∀ᶠ m : ℕ in atTop, 400 / Real.log 2 ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (400 / Real.log 2))
  filter_upwards [eventually_ge_atTop 1, hlarge] with m hm hmlarge
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmc : (400 : ℝ) ≤ (m : ℝ) * Real.log 2 := by
    have h := (div_le_iff₀ hlog2).mp hmlarge
    simpa [mul_comm] using h
  have hx_nonneg : 0 ≤ ((m : ℝ) * Real.log 2) / 10 := by positivity
  have hexp := Real.pow_div_factorial_le_exp
    (((m : ℝ) * Real.log 2) / 10) hx_nonneg 2
  norm_num at hexp
  have hlinear :
      ((m + 1 : ℕ) : ℝ) * Real.log 2 ≤
        (((m : ℝ) * Real.log 2) / 10) ^ 2 / 2 := by
    push_cast
    have hnonneg : 0 ≤ (m : ℝ) * Real.log 2 := by positivity
    have hquad :
        400 * ((m : ℝ) * Real.log 2) ≤
          ((m : ℝ) * Real.log 2) ^ 2 := by
      nlinarith
    nlinarith
  exact hlinear.trans hexp

/-- A sufficiently late power of two satisfies the source sequence-growth
condition `σᵢ₊₁ ≤ exp (σᵢ^(1/10))`. -/
theorem eventually_dyadicGrowthAdmissible :
    ∀ᶠ m : ℕ in atTop, DyadicGrowthAdmissible m := by
  filter_upwards [eventually_dyadic_log_growth] with m hm
  have hleft :
      ((2 ^ (m + 1) : ℕ) : ℝ) =
        Real.exp (((m + 1 : ℕ) : ℝ) * Real.log 2) := by
    push_cast
    rw [← Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 2) (m + 1)),
      Real.log_pow]
    push_cast
    rfl
  have hinner :
      (((2 ^ m : ℕ) : ℝ) ^ ((1 : ℝ) / 10)) =
        Real.exp (((m : ℝ) * Real.log 2) / 10) := by
    push_cast
    rw [Real.rpow_def_of_pos (pow_pos (by norm_num) m), Real.log_pow]
    congr 1
    push_cast
    ring
  rw [DyadicGrowthAdmissible, hleft, hinner]
  exact Real.exp_le_exp.mpr hm

/-- Threshold form of dyadic admissibility. -/
theorem exists_dyadic_admissibility_threshold :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → DyadicGrowthAdmissible m := by
  simpa only [eventually_atTop] using eventually_dyadicGrowthAdmissible

/-- A tail starting beyond any prescribed exponent is increasing, even, and
satisfies the growth hypothesis of Liu--Montgomery Corollary 1.3. -/
theorem exists_admissible_dyadic_tail (N : ℕ) :
    ∃ M : ℕ, N ≤ M ∧ 1 ≤ M ∧
      ∀ i : ℕ,
        Even (2 ^ (M + i)) ∧
        2 ^ (M + i) < 2 ^ (M + (i + 1)) ∧
        ((2 ^ (M + (i + 1)) : ℕ) : ℝ) ≤
          Real.exp (((2 ^ (M + i) : ℕ) : ℝ) ^ ((1 : ℝ) / 10)) := by
  obtain ⟨M₀, hM₀⟩ := exists_dyadic_admissibility_threshold
  let M := max M₀ (max N 1)
  refine ⟨M, le_max_of_le_right (le_max_left N 1),
    le_max_of_le_right (le_max_right N 1), ?_⟩
  intro i
  have hMpos : M + i ≠ 0 := by
    have : 1 ≤ M := le_max_of_le_right (le_max_right N 1)
    omega
  have heven : Even (2 ^ (M + i)) :=
    (Nat.even_pow).2 ⟨by norm_num, hMpos⟩
  have hstrict : 2 ^ (M + i) < 2 ^ (M + (i + 1)) := by
    rw [show M + (i + 1) = (M + i) + 1 by omega, pow_succ]
    have hpowpos : 0 < 2 ^ (M + i) := pow_pos (by norm_num) _
    omega
  have hMadm : DyadicGrowthAdmissible (M + i) := by
    apply hM₀
    have hM₀M : M₀ ≤ M := le_max_left M₀ (max N 1)
    omega
  refine ⟨heven, hstrict, ?_⟩
  simpa [DyadicGrowthAdmissible, Nat.add_assoc] using hMadm

end Erdos63.Parameters
