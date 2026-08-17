/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.RobustNumerics
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Eventual candidate-local geometry for source Lemma 3.7

This file proves the two pointwise route-loss estimates which accompany the
literal first-slow curve `floor (exp (ell^(1/16)))`.  The proof is kept
separate from the source pigeonhole estimates: it uses the actual candidate
radius through the lower bound `minRadius^2 <= s` and one global degree
threshold.
-/

open Filter Set

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

private noncomputable def lm37GeometryLogConstant : ℝ := 3000000000

private theorem lm37_firstSlow_monotone : Monotone lm37FirstSlowGrowth := by
  intro i j hij
  apply Nat.floor_mono
  apply Real.exp_monotone
  exact Real.rpow_le_rpow (Nat.cast_nonneg i) (by exact_mod_cast hij) (by norm_num)

/-- The natural floor loses at most one more than the corresponding real
increment. -/
private theorem lm37_firstSlow_stepLoss_cast_le {ell : ℕ} :
    (lm37FirstSlowStepLoss ell : ℝ) ≤
      Real.exp ((ell : ℝ) ^ ((1 : ℝ) / 16)) -
        Real.exp (((ell - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 16)) + 1 := by
  let x := Real.exp (((ell - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 16))
  let y := Real.exp ((ell : ℝ) ^ ((1 : ℝ) / 16))
  have hmono : lm37FirstSlowGrowth (ell - 1) ≤ lm37FirstSlowGrowth ell :=
    lm37_firstSlow_monotone (Nat.sub_le ell 1)
  have hy : (lm37FirstSlowGrowth ell : ℝ) ≤ y := by
    simpa only [lm37FirstSlowGrowth, y] using
      Nat.floor_le (Real.exp_pos _).le
  have hx : x < (lm37FirstSlowGrowth (ell - 1) : ℝ) + 1 := by
    simpa only [lm37FirstSlowGrowth, x] using
      Nat.lt_floor_add_one x
  rw [lm37FirstSlowStepLoss, Nat.cast_sub hmono]
  dsimp [x, y] at hx hy ⊢
  linarith

/-- One step in the sixteenth-root exponent is at most one. -/
private theorem lm37_rpow_step_le_one {ell : ℕ} (hell : 0 < ell) :
    (ell : ℝ) ^ ((1 : ℝ) / 16) ≤
      ((ell - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 16) + 1 := by
  have hdecomp : (ell : ℝ) = ((ell - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ ell)).symm
  rw [hdecomp]
  simpa using Real.rpow_add_le_add_rpow
    (show (0 : ℝ) ≤ ((ell - 1 : ℕ) : ℝ) by positivity)
    (show (0 : ℝ) ≤ 1 by norm_num)
    (show (0 : ℝ) ≤ (1 : ℝ) / 16 by norm_num)
    (show (1 : ℝ) / 16 ≤ 1 by norm_num)

/-- Mean-value estimate for one step of `exp (x^(1/16))`. -/
private theorem lm37_firstSlow_real_increment_le
    {ell : ℕ} (hell : 2 ≤ ell) :
    Real.exp ((ell : ℝ) ^ ((1 : ℝ) / 16)) -
        Real.exp (((ell - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 16)) ≤
      Real.exp ((ell : ℝ) ^ ((1 : ℝ) / 16)) *
        ((1 : ℝ) / 16) *
          (((ell - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 16)) ^ (-15 : ℤ) := by
  let x : ℝ := (ell - 1 : ℕ)
  let y : ℝ := ell
  let p : ℝ := (1 : ℝ) / 16
  let f : ℝ → ℝ := fun t ↦ Real.exp (t ^ p)
  let f' : ℝ → ℝ := fun t ↦ Real.exp (t ^ p) * (p * t ^ (p - 1))
  have hxy : x < y := by
    dsimp [x, y]
    exact_mod_cast (Nat.sub_lt (by omega : 0 < ell) (by omega : 0 < 1))
  have hcont : ContinuousOn f (Set.Icc x y) := by
    exact (Real.continuous_exp.comp
      (Real.continuous_rpow_const (by dsimp [p]; norm_num))).continuousOn
  have hderiv : ∀ t ∈ Set.Ioo x y, HasDerivAt f (f' t) t := by
    intro t ht
    have hxpos : 0 < x := by
      dsimp [x]
      exact_mod_cast (by omega : 0 < ell - 1)
    have htpos : 0 < t := hxpos.trans ht.1
    simpa only [f, f', mul_assoc] using
      (Real.hasDerivAt_rpow_const (x := t) (p := p) (Or.inl (ne_of_gt htpos))).exp
  obtain ⟨c, hc, hceq⟩ :=
    exists_hasDerivAt_eq_slope f f' hxy hcont hderiv
  have hwidth : y - x = 1 := by
    dsimp [x, y]
    rw [Nat.cast_sub (by omega : 1 ≤ ell)]
    norm_num
  have hdiff : f y - f x = f' c := by
    rw [hwidth, div_one] at hceq
    exact hceq.symm
  have hxpos : 0 < x := by
    dsimp [x]
    exact_mod_cast (by omega : 0 < ell - 1)
  have hcpos : 0 < c := hxpos.trans hc.1
  have hcy : c ≤ y := hc.2.le
  have hcx : x ≤ c := hc.1.le
  have hexp : Real.exp (c ^ p) ≤ Real.exp (y ^ p) := by
    apply Real.exp_le_exp.mpr
    exact Real.rpow_le_rpow hcpos.le hcy (by dsimp [p]; norm_num)
  have hneg : p - 1 = -(15 : ℝ) / 16 := by dsimp [p]; norm_num
  have hrpow : c ^ (p - 1) ≤ x ^ (p - 1) := by
    apply Real.rpow_le_rpow_of_nonpos
    · dsimp [x]
      exact_mod_cast (by omega : 0 < ell - 1)
    · exact hcx
    · dsimp [p]
      norm_num
  have hxrootpos : 0 < x ^ p := Real.rpow_pos_of_pos (by
    dsimp [x]
    exact_mod_cast (by omega : 0 < ell - 1)) _
  have hxpow : x ^ (p - 1) = (x ^ p) ^ (-15 : ℤ) := by
    calc
      x ^ (p - 1) = x ^ (p * (-15 : ℝ)) := by congr 1; dsimp [p]; norm_num
      _ = (x ^ p) ^ (-15 : ℝ) := Real.rpow_mul (by dsimp [x]; positivity) _ _
      _ = (x ^ p) ^ (-15 : ℤ) := by
        simpa using Real.rpow_intCast (x ^ p) (-15 : ℤ)
  rw [hdiff]
  dsimp [f, f', x, y, p]
  rw [hxpow] at hrpow
  have hpnonneg : (0 : ℝ) ≤ 1 / 16 := by norm_num
  have hpc : ((1 : ℝ) / 16) * c ^ (((1 : ℝ) / 16) - 1) ≤
      ((1 : ℝ) / 16) *
        (((ell - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 16)) ^ (-15 : ℤ) := by
    simpa only [p, x] using mul_le_mul_of_nonneg_left hrpow hpnonneg
  calc
    Real.exp (c ^ ((1 : ℝ) / 16)) *
        (((1 : ℝ) / 16) * c ^ (((1 : ℝ) / 16) - 1)) ≤
        Real.exp (((ell : ℕ) : ℝ) ^ ((1 : ℝ) / 16)) *
          (((1 : ℝ) / 16) * c ^ (((1 : ℝ) / 16) - 1)) :=
      mul_le_mul_of_nonneg_right hexp
        (mul_nonneg hpnonneg (Real.rpow_nonneg hcpos.le _))
    _ ≤ Real.exp (((ell : ℕ) : ℝ) ^ ((1 : ℝ) / 16)) *
          (((1 : ℝ) / 16) *
            (((ell - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 16)) ^ (-15 : ℤ)) :=
      mul_le_mul_of_nonneg_left hpc (Real.exp_pos _).le
    _ = _ := by ring

/-- A slow value controls the clock: the preceding sixteenth root is below
`log s`, and consequently the clock itself is below `2 * log(s)^16`.
Keeping this as a real estimate avoids all floor/ceiling noise in the route
budget. -/
private theorem lm37_firstSlow_clock_le
    {ell s : ℕ} (hell : 0 < ell)
    (hslow : lm37FirstSlowGrowth (ell - 1) < s)
    (hlog : 1 ≤ Real.log (s : ℝ)) :
    (ell : ℝ) ≤ 2 * Real.log (s : ℝ) ^ 16 := by
  let b : ℝ := ((ell - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 16)
  have hspos : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hexpFloor : Real.exp b < (lm37FirstSlowGrowth (ell - 1) : ℝ) + 1 := by
    simpa only [b, lm37FirstSlowGrowth] using
      Nat.lt_floor_add_one (Real.exp b)
  have hfloorSucc : lm37FirstSlowGrowth (ell - 1) + 1 ≤ s := by omega
  have hexp : Real.exp b < (s : ℝ) :=
    hexpFloor.trans_le (by exact_mod_cast hfloorSucc)
  have hbLog : b < Real.log (s : ℝ) :=
    (Real.lt_log_iff_exp_lt hspos).2 hexp
  have hbnonneg : 0 ≤ b := by dsimp [b]; positivity
  have hbpow : b ^ 16 = ((ell - 1 : ℕ) : ℝ) := by
    dsimp [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hpow : b ^ 16 ≤ Real.log (s : ℝ) ^ 16 := by
    exact pow_le_pow_left₀ hbnonneg hbLog.le 16
  have hellCast : (ell : ℝ) = ((ell - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ ell)).symm
  rw [hellCast, ← hbpow]
  have hlogpow : 1 ≤ Real.log (s : ℝ) ^ 16 := one_le_pow₀ hlog
  linarith

/-- The natural square root lies below the real square root. -/
private theorem natSqrt_cast_le_realSqrt (s : ℕ) :
    (Nat.sqrt s : ℝ) ≤ Real.sqrt (s : ℝ) := by
  apply (Real.le_sqrt (by positivity) (by positivity)).2
  have h : ((Nat.sqrt s : ℝ) ^ 2) ≤ (s : ℝ) := by
    exact_mod_cast Nat.sqrt_le' s
  simpa [pow_two] using h

private theorem lm37_routeRest_le
    {s Q ell : ℕ} {L : ℝ}
    (hQnonneg : (0 : ℝ) ≤ Q)
    (hclockReal : (ell : ℝ) ≤ 2 * L ^ 16)
    (hsqrtReal : (Nat.sqrt s : ℝ) ≤ Real.sqrt (s : ℝ))
    (hQroot : 100 * (Q : ℝ) ≤ Real.sqrt (s : ℝ))
    (hpoly : (Q : ℝ) * (4 * L ^ 16 + 2) ≤ (s : ℝ) / 4)
    (hLone : 1 ≤ L) :
    (Q : ℝ) * ((11 * Nat.sqrt s + 1 : ℕ) + 2 * ell) ≤
      (s : ℝ) / 2 := by
  have hsqrtSq : Real.sqrt (s : ℝ) ^ 2 = (s : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg s)
  have hsqrtPart : (Q : ℝ) * (11 * Real.sqrt (s : ℝ)) ≤
      (s : ℝ) / 8 := by
    have hmul := mul_le_mul_of_nonneg_right hQroot (Real.sqrt_nonneg (s : ℝ))
    nlinarith [mul_nonneg hQnonneg (Real.sqrt_nonneg (s : ℝ))]
  have hinside : 1 + 2 * (ell : ℝ) ≤ 4 * L ^ 16 + 2 := by
    nlinarith [hclockReal, one_le_pow₀ hLone (n := 16)]
  have hrestPoly : (Q : ℝ) * (1 + 2 * (ell : ℝ)) ≤
      (s : ℝ) / 4 :=
    (mul_le_mul_of_nonneg_left hinside hQnonneg).trans hpoly
  push_cast
  have hsqrtNat : (Q : ℝ) * (11 * (Nat.sqrt s : ℝ)) ≤
      (s : ℝ) / 8 := by
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsqrtReal (by norm_num)) hQnonneg).trans hsqrtPart
  nlinarith

private theorem lm37_step_low_le
    {s Q ell : ℕ} {a : ℝ}
    (hQnonneg : (0 : ℝ) ≤ Q)
    (hstepExp : (lm37FirstSlowStepLoss ell : ℝ) ≤ Real.exp a)
    (hexpa : Real.exp a ≤ 3 * Real.sqrt (s : ℝ))
    (hQroot : 100 * (Q : ℝ) ≤ Real.sqrt (s : ℝ)) :
    (Q : ℝ) * (lm37FirstSlowStepLoss ell : ℝ) ≤ (s : ℝ) / 2 := by
  have hstrong : 6 * (Q : ℝ) ≤ Real.sqrt (s : ℝ) := by nlinarith
  have hsqrtSq := Real.sq_sqrt (Nat.cast_nonneg s)
  calc
    (Q : ℝ) * (lm37FirstSlowStepLoss ell : ℝ) ≤
        (Q : ℝ) * (3 * Real.sqrt (s : ℝ)) :=
      mul_le_mul_of_nonneg_left (hstepExp.trans hexpa) hQnonneg
    _ ≤ (s : ℝ) / 2 := by
      nlinarith [hstrong, hsqrtSq, Real.sqrt_nonneg (s : ℝ), hQnonneg]

private theorem lm37_step_high_le
    {s Q ell : ℕ} {C L a b : ℝ}
    (hC : 0 < C) (hLone : 1 ≤ L) (hLlarge : 100000 * C ≤ L)
    (hQ : (Q : ℝ) ≤ C * L ^ 4)
    (hQroot : 100 * (Q : ℝ) ≤ Real.sqrt (s : ℝ))
    (hbpos : 0 < b) (hbLower : L / 2 < b)
    (hexpa : Real.exp a ≤ 3 * (s : ℝ))
    (hstepReal : (lm37FirstSlowStepLoss ell : ℝ) ≤
      Real.exp a - Real.exp b + 1)
    (hincrement : Real.exp a - Real.exp b ≤
      Real.exp a * ((1 : ℝ) / 16) * b ^ (-15 : ℤ)) :
    (Q : ℝ) * (lm37FirstSlowStepLoss ell : ℝ) ≤ (s : ℝ) / 2 := by
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hbInv : b ^ (-15 : ℤ) ≤ (2 ^ 15 : ℝ) / L ^ 15 := by
    rw [show (-15 : ℤ) = Int.negSucc 14 by rfl, zpow_negSucc]
    rw [inv_eq_one_div,
      div_le_div_iff₀ (pow_pos hbpos 15) (pow_pos hLpos 15)]
    have hpow : (L / 2) ^ 15 ≤ b ^ 15 :=
      pow_le_pow_left₀ (by positivity) hbLower.le 15
    calc
      1 * L ^ 15 = 2 ^ 15 * (L / 2) ^ 15 := by ring
      _ ≤ 2 ^ 15 * b ^ 15 := by gcongr
  have hstepFormula : (lm37FirstSlowStepLoss ell : ℝ) ≤
      6144 * (s : ℝ) / L ^ 15 + 1 := by
    calc
      (lm37FirstSlowStepLoss ell : ℝ) ≤
          Real.exp a - Real.exp b + 1 := hstepReal
      _ ≤ Real.exp a * (1 / 16 : ℝ) * b ^ (-15 : ℤ) + 1 := by
        linarith
      _ ≤ (3 * (s : ℝ)) * (1 / 16 : ℝ) *
          ((2 ^ 15 : ℝ) / L ^ 15) + 1 := by gcongr
      _ = 6144 * (s : ℝ) / L ^ 15 + 1 := by ring
  have hderivCoeff : 24576 * C ≤ L ^ 11 := by
    have hLpow : L ≤ L ^ 11 := by
      simpa [pow_one] using pow_le_pow_right₀ hLone (by omega : 1 ≤ 11)
    have hconst : 24576 * C ≤ 100000 * C :=
      mul_le_mul_of_nonneg_right (by norm_num) hC.le
    exact hconst.trans (hLlarge.trans hLpow)
  have hmain : (Q : ℝ) * (6144 * (s : ℝ) / L ^ 15) ≤
      (s : ℝ) / 4 := by
    have hL15pos : 0 < L ^ 15 := pow_pos hLpos 15
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    rw [div_eq_mul_inv]
    calc
      (Q : ℝ) * (6144 * (s : ℝ) * (L ^ 15)⁻¹) * 4 =
          ((Q : ℝ) * 24576 / L ^ 15) * (s : ℝ) := by ring
      _ ≤ (s : ℝ) := by
        have hfrac : (Q : ℝ) * 24576 / L ^ 15 ≤ 1 := by
          rw [div_le_one hL15pos]
          calc
            (Q : ℝ) * 24576 ≤ C * L ^ 4 * 24576 := by gcongr
            _ = (24576 * C) * L ^ 4 := by ring
            _ ≤ L ^ 11 * L ^ 4 := by gcongr
            _ = L ^ 15 := by ring
        simpa using mul_le_mul_of_nonneg_right hfrac (Nat.cast_nonneg s)
  have hone : (Q : ℝ) ≤ (s : ℝ) / 4 := by
    have hfourQ : 4 * (Q : ℝ) ≤ Real.sqrt (s : ℝ) := by linarith [hQroot]
    have hsqrtLe : Real.sqrt (s : ℝ) ≤ (s : ℝ) :=
      Real.sqrt_le_self_iff.mpr (by
        by_cases hs0 : s = 0
        · exact Or.inl (by exact_mod_cast hs0)
        · exact Or.inr (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs0))
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    simpa [mul_comm] using hfourQ.trans hsqrtLe
  calc
    (Q : ℝ) * (lm37FirstSlowStepLoss ell : ℝ) ≤
        (Q : ℝ) * (6144 * (s : ℝ) / L ^ 15 + 1) := by gcongr
    _ = (Q : ℝ) * (6144 * (s : ℝ) / L ^ 15) + (Q : ℝ) := by ring
    _ ≤ (s : ℝ) / 4 + (s : ℝ) / 4 := add_le_add hmain hone
    _ = (s : ℝ) / 2 := by ring

private theorem lm37_combine_route_step
    {s Q ell : ℕ}
    (hroute : (Q : ℝ) * ((11 * Nat.sqrt s + 1 : ℕ) + 2 * ell) ≤
      (s : ℝ) / 2)
    (hstep : (Q : ℝ) * (lm37FirstSlowStepLoss ell : ℝ) ≤
      (s : ℝ) / 2) :
    Q * (lm37FirstSlowStepLoss ell + (11 * Nat.sqrt s + 1) + 2 * ell) ≤ s := by
  have htotalReal :
      ((Q * (lm37FirstSlowStepLoss ell +
        (11 * Nat.sqrt s + 1) + 2 * ell) : ℕ) : ℝ) ≤ (s : ℝ) := by
    push_cast at hroute
    push_cast
    calc
      (Q : ℝ) * ((lm37FirstSlowStepLoss ell : ℝ) +
          (11 * (Nat.sqrt s : ℝ) + 1) + 2 * (ell : ℝ)) =
          (Q : ℝ) * (lm37FirstSlowStepLoss ell : ℝ) +
            (Q : ℝ) * ((11 * (Nat.sqrt s : ℝ) + 1) + 2 * (ell : ℝ)) := by ring
      _ ≤ (s : ℝ) / 2 + (s : ℝ) / 2 := add_le_add hstep hroute
      _ = (s : ℝ) := by ring
  exact_mod_cast htotalReal

/-- Uniform route arithmetic once the relevant growth divisor is bounded by
`C * log(s)^4`.  This is the common analytic core of the small and large
source branches. -/
theorem eventually_lm37_firstSlow_route_of_divisor_log_bound
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ s : ℕ in atTop, ∀ Q ell : ℕ,
      (Q : ℝ) ≤ C * Real.log (s : ℝ) ^ 4 →
      0 < ell → lm37FirstSlowGrowth (ell - 1) < s →
      Q * (lm37FirstSlowStepLoss ell + (11 * Nat.sqrt s + 1) + 2 * ell) ≤ s := by
  have hlog : Tendsto (fun s : ℕ ↦ Real.log (s : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrt := tendsto_natCast_atTop_atTop.eventually
    (Parameters.eventually_const_mul_log_pow_le_self
      ((100 * C) ^ 2) 8)
  have hclock := tendsto_natCast_atTop_atTop.eventually
    (Parameters.eventually_const_mul_log_pow_le_self
      (100 * C) 20)
  filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ)),
      hlog.eventually (eventually_ge_atTop (100000 * C)),
      hsqrt, hclock, eventually_ge_atTop (4 : ℕ)]
    with s hL hLlarge hsqrtBound hclockBound hsFour
  intro Q ell hQ hell hslow
  let L : ℝ := Real.log (s : ℝ)
  let a : ℝ := (ell : ℝ) ^ ((1 : ℝ) / 16)
  let b : ℝ := ((ell - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 16)
  have hLone : 1 ≤ L := by simpa only [L] using hL
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hspos : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hQnonneg : (0 : ℝ) ≤ Q := by positivity
  have hclockReal : (ell : ℝ) ≤ 2 * L ^ 16 := by
    simpa only [L] using lm37_firstSlow_clock_le hell hslow hLone
  have hsqrtReal : (Nat.sqrt s : ℝ) ≤ Real.sqrt (s : ℝ) :=
    natSqrt_cast_le_realSqrt s
  have hroot : (100 * C * L ^ 4) ^ 2 ≤ (s : ℝ) := by
    calc
      (100 * C * L ^ 4) ^ 2 = (100 * C) ^ 2 * L ^ 8 := by ring
      _ ≤ (s : ℝ) := by simpa only [L] using hsqrtBound
  have hQbase : 100 * (Q : ℝ) ≤ 100 * C * L ^ 4 := by nlinarith
  have hQroot : 100 * (Q : ℝ) ≤ Real.sqrt (s : ℝ) := by
    apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg s)).2
    exact (pow_le_pow_left₀ (by positivity) hQbase 2).trans hroot
  have hpoly : (Q : ℝ) * (4 * L ^ 16 + 2) ≤ (s : ℝ) / 4 := by
    have htwenty : L ^ 4 * (4 * L ^ 16 + 2) ≤ 6 * L ^ 20 := by
      have hpow4_20 : L ^ 4 ≤ L ^ 20 := pow_le_pow_right₀ hLone (by omega)
      nlinarith [pow_nonneg hLpos.le 4, pow_nonneg hLpos.le 16]
    calc
      (Q : ℝ) * (4 * L ^ 16 + 2) ≤
          C * L ^ 4 * (4 * L ^ 16 + 2) := by gcongr
      _ = C * (L ^ 4 * (4 * L ^ 16 + 2)) := by ring
      _ ≤ C * (6 * L ^ 20) := mul_le_mul_of_nonneg_left htwenty hC.le
      _ ≤ (s : ℝ) / 4 := by
        have hclock' : 100 * C * L ^ 20 ≤ (s : ℝ) := by
          simpa only [L] using hclockBound
        nlinarith [mul_nonneg hC.le (pow_nonneg hLpos.le 20)]
  have hrouteRest :
      (Q : ℝ) * ((11 * Nat.sqrt s + 1 : ℕ) + 2 * ell) ≤
        (s : ℝ) / 2 :=
    lm37_routeRest_le hQnonneg hclockReal hsqrtReal hQroot hpoly hLone
  have hstep : (Q : ℝ) * (lm37FirstSlowStepLoss ell : ℝ) ≤
      (s : ℝ) / 2 := by
    by_cases hellOne : ell = 1
    · subst ell
      have hstepOne : lm37FirstSlowStepLoss 1 ≤ 2 := by
        simp only [lm37FirstSlowStepLoss, Nat.reduceSubDiff]
        have hfloor : lm37FirstSlowGrowth 1 ≤ 2 := by
          apply Nat.le_of_lt_succ
          rw [lm37FirstSlowGrowth, Nat.floor_lt (Real.exp_pos _).le]
          norm_num
          exact Real.exp_one_lt_d9.trans (by norm_num)
        omega
      have hsqrtLe : Real.sqrt (s : ℝ) ≤ (s : ℝ) / 2 := by
        have hsqrtSq := Real.sq_sqrt (Nat.cast_nonneg s)
        have : (4 : ℝ) ≤ s := by exact_mod_cast hsFour
        nlinarith [Real.sqrt_nonneg (s : ℝ)]
      have hstepCast : (lm37FirstSlowStepLoss 1 : ℝ) ≤ 2 := by exact_mod_cast hstepOne
      calc
        (Q : ℝ) * (lm37FirstSlowStepLoss 1 : ℝ) ≤ (Q : ℝ) * 2 := by gcongr
        _ ≤ Real.sqrt (s : ℝ) := by nlinarith
        _ ≤ (s : ℝ) / 2 := hsqrtLe
    · have hellTwo : 2 ≤ ell := by omega
      have hstepReal := lm37_firstSlow_stepLoss_cast_le (ell := ell)
      have hincrement := lm37_firstSlow_real_increment_le hellTwo
      have hab : a ≤ b + 1 := by
        simpa only [a, b] using lm37_rpow_step_le_one hell
      have hexpFloor : Real.exp b < (lm37FirstSlowGrowth (ell - 1) : ℝ) + 1 := by
        simpa only [b, lm37FirstSlowGrowth] using
          Nat.lt_floor_add_one (Real.exp b)
      have hfloorSucc : lm37FirstSlowGrowth (ell - 1) + 1 ≤ s := by omega
      have hexpb : Real.exp b < (s : ℝ) :=
        hexpFloor.trans_le (by exact_mod_cast hfloorSucc)
      have hbLog : b < L := by
        exact (Real.lt_log_iff_exp_lt hspos).2 (by simpa only [L] using hexpb)
      have hbpos : 0 < b := by
        dsimp [b]
        exact Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < ell - 1)) _
      by_cases hbHalf : b ≤ L / 2
      · have hexpa : Real.exp a ≤ 3 * Real.sqrt (s : ℝ) := by
          calc
            Real.exp a ≤ Real.exp (b + 1) := Real.exp_le_exp.mpr hab
            _ = Real.exp b * Real.exp 1 := by rw [Real.exp_add]
            _ ≤ Real.sqrt (s : ℝ) * 3 := by
              gcongr
              · rw [Real.sqrt_eq_rpow]
                rw [Real.rpow_def_of_pos hspos]
                exact Real.exp_le_exp.mpr (by dsimp [L] at hbHalf ⊢; linarith)
              · exact Real.exp_one_lt_d9.le.trans (by norm_num)
            _ = 3 * Real.sqrt (s : ℝ) := by ring
        have hstepExp : (lm37FirstSlowStepLoss ell : ℝ) ≤ Real.exp a := by
          calc
            (lm37FirstSlowStepLoss ell : ℝ) ≤
                (lm37FirstSlowGrowth ell : ℝ) := by exact_mod_cast Nat.sub_le _ _
            _ ≤ Real.exp a := by
              simpa only [a, lm37FirstSlowGrowth] using
                Nat.floor_le (Real.exp_pos _).le
        exact lm37_step_low_le hQnonneg hstepExp hexpa hQroot
      · have hbLower : L / 2 < b := lt_of_not_ge hbHalf
        have hexpa : Real.exp a ≤ 3 * (s : ℝ) := by
          calc
            Real.exp a ≤ Real.exp (b + 1) := Real.exp_le_exp.mpr hab
            _ = Real.exp b * Real.exp 1 := by rw [Real.exp_add]
            _ ≤ (s : ℝ) * 3 := by
              exact mul_le_mul hexpb.le (Real.exp_one_lt_d9.le.trans (by norm_num))
                (Real.exp_pos _).le (Nat.cast_nonneg s)
            _ = 3 * (s : ℝ) := by ring
        exact lm37_step_high_le hC hLone (by simpa only [L] using hLlarge)
          hQ hQroot hbpos hbLower hexpa
          (by simpa only [a, b] using hstepReal)
          (by simpa only [a, b] using hincrement)
  exact lm37_combine_route_step hrouteRest hstep

end Erdos63
