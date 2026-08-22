/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZGapBetaArithmetic

/-!
# Uniform numerical bookkeeping for the HLOZ deficit bands

This file contains the real-variable part of Lemma 4.10 which is independent
of the stopped-path decomposition.  In particular it bounds the logarithm of
the literal Proposition 4.8 candidate budget and records the power separation
which absorbs both that logarithm and the final `log m` squared target.
-/

open Filter Real
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZGapBetaNumerics

open HLOZGapBetaArithmetic HLOZGapMeshEscape HLOZPathEvents
  HLOZProposition48Candidates ScreeningInstantiation

noncomputable section

/-- At a fixed level at least one, the explicit Proposition 4.8 candidate
budget is monotone in its deficit exponent.  This permits the final deficit
band to be clipped at exponent `1`, while comparing it to the next point of
the affine beta mesh. -/
theorem candidateBudget48_mono_beta
    {m : ℕ} (hm : 1 ≤ m) {beta gamma : ℝ} (hbeta : beta ≤ gamma) :
    candidateBudget48 m beta ≤ candidateBudget48 m gamma := by
  unfold candidateBudget48
  apply Nat.ceil_mono
  unfold candidateBudgetReal48
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : (m : ℝ) ^ (beta - kappaOne) ≤
      (m : ℝ) ^ (gamma - kappaOne) :=
    Real.rpow_le_rpow_of_exponent_le hmR (by linarith)
  gcongr
  exact candidateExponent48_pos.le

/-- For a valid escape probability, requiring more returns can only decrease
the literal geometric-return cost. -/
theorem geometricReturnCost_anti_returns
    {escapeChance : ℝ} (hzero : 0 ≤ escapeChance)
    (hone : escapeChance ≤ 1) {lower upper : ℕ} (hreturns : lower ≤ upper) :
    Gap.geometricReturnCost escapeChance upper ≤
      Gap.geometricReturnCost escapeChance lower := by
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_of_le_one (sub_nonneg.mpr hone)
    (by linarith) hreturns

/-- A convenient logarithmic upper bound for the integer Proposition 4.8
budget.  The estimate is intentionally coarse; its three terms retain the
only asymptotic information subsequently used. -/
theorem log_candidateBudget48_le
    {m : ℕ} {beta gamma : ℝ} (hm : 3 ≤ m)
    (hbeta : beta - kappaOne = gamma) (hgamma : 0 ≤ gamma) :
    Real.log (candidateBudget48 m beta) ≤
      Real.log 12 + candidateExponent48 * (m : ℝ) ^ gamma +
        2 * Real.log (Real.log (m : ℝ)) := by
  have hmR : (1 : ℝ) < m := by
    exact_mod_cast (show 1 < m by omega)
  have hlog : 1 < Real.log (m : ℝ) := by
    apply (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < m)).2
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hm)
  have hpow : 1 ≤ (m : ℝ) ^ gamma := by
    exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) hgamma
  have hrealPos : 1 ≤ candidateBudgetReal48 m beta := by
    unfold candidateBudgetReal48
    have hexp : 1 ≤ Real.exp
        (candidateExponent48 * (m : ℝ) ^ (beta - kappaOne)) :=
      Real.one_le_exp (mul_nonneg candidateExponent48_pos.le
        (Real.rpow_nonneg (by positivity) _))
    nlinarith [sq_nonneg (Real.log (m : ℝ))]
  have hceil : (candidateBudget48 m beta : ℝ) ≤
      2 * candidateBudgetReal48 m beta := by
    unfold candidateBudget48
    have hlt := Nat.ceil_lt_add_one (show 0 ≤ candidateBudgetReal48 m beta by
      exact hrealPos.trans' zero_le_one)
    have hle : (Nat.ceil (candidateBudgetReal48 m beta) : ℝ) ≤
        candidateBudgetReal48 m beta + 1 := hlt.le
    linarith
  have hbudgetPos : (0 : ℝ) < candidateBudget48 m beta := by
    exact_mod_cast HLOZGapBetaArithmetic.candidateBudget48_pos
      (show 1 < m by omega : 1 < m) (beta := beta)
  have hupperPos : (0 : ℝ) < 2 * candidateBudgetReal48 m beta := by
    positivity
  calc
    Real.log (candidateBudget48 m beta) ≤
        Real.log (2 * candidateBudgetReal48 m beta) :=
      Real.log_le_log hbudgetPos hceil
    _ = Real.log 12 + candidateExponent48 * (m : ℝ) ^ gamma +
        2 * Real.log (Real.log (m : ℝ)) := by
      rw [candidateBudgetReal48, hbeta]
      rw [show 2 * (6 * Real.exp
          (candidateExponent48 * (m : ℝ) ^ gamma) *
          Real.log (m : ℝ) ^ 2) =
          12 * Real.exp (candidateExponent48 * (m : ℝ) ^ gamma) *
            Real.log (m : ℝ) ^ 2 by ring]
      rw [Real.log_mul
        (mul_ne_zero (by norm_num : (12 : ℝ) ≠ 0) (Real.exp_ne_zero _))
        (pow_ne_zero 2 (ne_of_gt (zero_lt_one.trans hlog)))]
      rw [Real.log_mul (by norm_num : (12 : ℝ) ≠ 0)
        (Real.exp_ne_zero _), Real.log_exp, Real.log_pow]
      ring

/-- Every fixed multiple of `log m` squared is eventually absorbed by any
positive power of `m`. -/
theorem eventually_const_mul_log_sq_le_nat_rpow
    (C epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ m : ℕ in atTop,
      C * Real.log (m : ℝ) ^ 2 ≤ (m : ℝ) ^ epsilon := by
  let q : ℝ := epsilon / 4
  let K : ℝ := max C 0 * (1 / q) ^ 2
  have hq : 0 < q := by dsimp only [q]; linarith
  have habsorb :=
    ExternalProposition44.eventually_const_mul_nat_rpow_le K
      (epsilon / 2) epsilon (by linarith)
  filter_upwards [habsorb, eventually_ge_atTop 1] with m habsorbM hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog0 : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm)
  have hmqPos : 0 < (m : ℝ) ^ q := Real.rpow_pos_of_pos hmR q
  have hlogBound : q * Real.log (m : ℝ) ≤ (m : ℝ) ^ q := by
    calc
      q * Real.log (m : ℝ) = Real.log ((m : ℝ) ^ q) :=
        (Real.log_rpow hmR q).symm
      _ ≤ (m : ℝ) ^ q - 1 := Real.log_le_sub_one_of_pos hmqPos
      _ ≤ (m : ℝ) ^ q := by linarith
  have hlogLe : Real.log (m : ℝ) ≤ (1 / q) * (m : ℝ) ^ q := by
    calc
      Real.log (m : ℝ) = (1 / q) * (q * Real.log (m : ℝ)) := by
        field_simp
      _ ≤ (1 / q) * (m : ℝ) ^ q := by
        exact mul_le_mul_of_nonneg_left hlogBound (by positivity)
  have hpowSq : ((m : ℝ) ^ q) ^ 2 = (m : ℝ) ^ (epsilon / 2) := by
    calc
      ((m : ℝ) ^ q) ^ 2 = ((m : ℝ) ^ q) ^ (2 : ℝ) :=
        (Real.rpow_natCast ((m : ℝ) ^ q) 2).symm
      _ = (m : ℝ) ^ (q * 2) :=
        (Real.rpow_mul hmR.le q 2).symm
      _ = (m : ℝ) ^ (epsilon / 2) := by
        congr 1
        dsimp only [q]
        ring
  have hlogSq : Real.log (m : ℝ) ^ 2 ≤
      (1 / q) ^ 2 * (m : ℝ) ^ (epsilon / 2) := by
    calc
      Real.log (m : ℝ) ^ 2 ≤
          ((1 / q) * (m : ℝ) ^ q) ^ 2 :=
        pow_le_pow_left₀ hlog0 hlogLe 2
      _ = (1 / q) ^ 2 * (m : ℝ) ^ (epsilon / 2) := by
        rw [mul_pow, hpowSq]
  have hCK : C * Real.log (m : ℝ) ^ 2 ≤
      K * (m : ℝ) ^ (epsilon / 2) := by
    have hCmax : C ≤ max C 0 := le_max_left _ _
    have hmax0 : 0 ≤ max C 0 := le_max_right _ _
    calc
      C * Real.log (m : ℝ) ^ 2 ≤
          max C 0 * Real.log (m : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hCmax (sq_nonneg _)
      _ ≤ max C 0 *
          ((1 / q) ^ 2 * (m : ℝ) ^ (epsilon / 2)) :=
        mul_le_mul_of_nonneg_left hlogSq hmax0
      _ = K * (m : ℝ) ^ (epsilon / 2) := by
        dsimp only [K]
        ring
  exact hCK.trans habsorbM

/-- The logarithmic point-escape cost on mesh cell `a` is bounded below by
the reciprocal of a fixed multiple of `m ^ meshExponent a`.  The constant
is deliberately loose: it absorbs the ceiling in the mesh radius and all
fixed factors in `pointBeforeReturnLogScale`. -/
theorem one_div_two_hundred_nat_rpow_meshExponent_le_meshPointEscapeChance
    {m : ℕ} (hm : 1 ≤ m) (a : GapScale) :
    1 / (200 * (m : ℝ) ^ meshExponent a) ≤ meshPointEscapeChance m a := by
  let p : ℝ := (m : ℝ) ^ meshExponent a
  let R : ℝ := Real.exp p
  have halpha : 0 ≤ meshExponent a := by
    unfold meshExponent
    have : (0 : ℝ) ≤ (a : ℕ) + 1 := by positivity
    exact mul_nonneg this (by norm_num [meshDelta])
  have hp : 1 ≤ p := by
    exact Real.one_le_rpow (by exact_mod_cast hm) halpha
  have hR : 1 ≤ R := Real.one_le_exp (zero_le_one.trans hp)
  have hradius : meshRadius m a = R := by
    rfl
  have hceil : (Nat.ceil R : ℝ) < R + 1 :=
    Nat.ceil_lt_add_one (Real.exp_nonneg p)
  have hceilTwo : (Nat.ceil R : ℝ) ≤ 2 * R := by
    linarith
  have hbase : (4 : ℝ) * Nat.ceil R + 3 ≤ 11 * R := by
    nlinarith
  have hscale : (meshPointBeforeReturnLogScale m a : ℝ) ≤
      24 * (11 * R) ^ 3 := by
    unfold meshPointBeforeReturnLogScale
    push_cast
    rw [hradius]
    gcongr
  have hscalePos : (0 : ℝ) < meshPointBeforeReturnLogScale m a := by
    exact_mod_cast meshPointBeforeReturnLogScale_pos m a
  have hupperPos : (0 : ℝ) < 24 * (11 * R) ^ 3 := by
    positivity
  have hlogScale :
      Real.log (meshPointBeforeReturnLogScale m a : ℝ) ≤
        Real.log 24 + 3 * (Real.log 11 + p) := by
    calc
      Real.log (meshPointBeforeReturnLogScale m a : ℝ) ≤
          Real.log (24 * (11 * R) ^ 3) :=
        Real.log_le_log hscalePos hscale
      _ = Real.log 24 + 3 * (Real.log 11 + p) := by
        rw [Real.log_mul (by norm_num : (24 : ℝ) ≠ 0)
          (pow_ne_zero 3 (mul_ne_zero (by norm_num : (11 : ℝ) ≠ 0)
            (Real.exp_ne_zero p))), Real.log_pow,
          Real.log_mul (by norm_num : (11 : ℝ) ≠ 0) (Real.exp_ne_zero p),
          Real.log_exp]
        ring
  have hlogTwentyFour : Real.log (24 : ℝ) ≤ 23 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 24)
    norm_num at h ⊢
    exact h
  have hlogEleven : Real.log (11 : ℝ) ≤ 10 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11)
    norm_num at h ⊢
    exact h
  have hdenominator :
      4 + 2 * Real.log (meshPointBeforeReturnLogScale m a : ℝ) ≤
        200 * p := by
    nlinarith
  have hdenominatorPos :
      0 < 4 + 2 * Real.log (meshPointBeforeReturnLogScale m a : ℝ) := by
    have hscaleOne : (1 : ℝ) ≤ meshPointBeforeReturnLogScale m a := by
      exact_mod_cast meshPointBeforeReturnLogScale_pos m a
    have := Real.log_nonneg hscaleOne
    linarith
  unfold meshPointEscapeChance
  change 1 / (200 * p) ≤
    1 / (4 + 2 * Real.log (meshPointBeforeReturnLogScale m a : ℝ))
  exact one_div_le_one_div_of_le hdenominatorPos hdenominator

/-- Removing the first hit from a ceiling loses at most half of a real
return budget once that budget is at least two. -/
theorem half_nat_rpow_le_requiredReturns48
    {m : ℕ} {beta : ℝ} (hpow : 2 ≤ (m : ℝ) ^ beta) :
    (1 / 2 : ℝ) * (m : ℝ) ^ beta ≤ requiredReturns48 m beta := by
  have hpos : 0 < (m : ℝ) ^ beta := lt_of_lt_of_le (by norm_num) hpow
  have hceil := Nat.le_ceil ((m : ℝ) ^ beta)
  have hadd := requiredReturns48_add_one (m := m) (beta := beta) hpos
  have hcast : ((requiredReturns48 m beta : ℕ) : ℝ) + 1 =
      (Nat.ceil ((m : ℝ) ^ beta) : ℝ) := by
    exact_mod_cast hadd
  rw [← hcast] at hceil
  norm_num at hceil ⊢
  linarith

/-- Product form of the preceding two elementary estimates.  It is the
precise lower bound needed to turn beta-exponent separation into a geometric
return cost. -/
theorem one_div_four_hundred_nat_rpow_sub_le_escape_mul_requiredReturns48
    {m : ℕ} {beta : ℝ} (hm : 1 ≤ m) (a : GapScale)
    (hreturns : 2 ≤ (m : ℝ) ^ beta) :
    (1 / 400 : ℝ) * (m : ℝ) ^ (beta - meshExponent a) ≤
      meshPointEscapeChance m a * requiredReturns48 m beta := by
  have hmPos : (0 : ℝ) < m := by
    exact_mod_cast (zero_lt_one.trans_le hm)
  have hmeshPowPos : 0 < (m : ℝ) ^ meshExponent a :=
    Real.rpow_pos_of_pos hmPos _
  have hescape :=
    one_div_two_hundred_nat_rpow_meshExponent_le_meshPointEscapeChance hm a
  have hreturn := half_nat_rpow_le_requiredReturns48 hreturns
  have hproduct :
      (1 / (200 * (m : ℝ) ^ meshExponent a)) *
          ((1 / 2 : ℝ) * (m : ℝ) ^ beta) ≤
        meshPointEscapeChance m a * requiredReturns48 m beta := by
    exact mul_le_mul hescape hreturn (by positivity)
      (meshPointEscapeChance_pos m a).le
  calc
    (1 / 400 : ℝ) * (m : ℝ) ^ (beta - meshExponent a) =
        (1 / (200 * (m : ℝ) ^ meshExponent a)) *
          ((1 / 2 : ℝ) * (m : ℝ) ^ beta) := by
      rw [Real.rpow_sub hmPos]
      field_simp
      ring
    _ ≤ meshPointEscapeChance m a * requiredReturns48 m beta := hproduct

/-- The decisive numerical comparison for one adjacent HLOZ beta band.  If
`gamma = beta - kappaOne`, then the candidate logarithm and an arbitrary
fixed multiple of `log m` squared are swallowed by the extra mesh power
`m^meshDelta`.  The explicit factor `1/1000` leaves room for the elementary
escape-probability and ceiling losses in the stopped return certificate. -/
theorem eventually_log_candidateBudget48_add_log_sq_le
    (beta gamma targetCoefficient : ℝ)
    (hbeta : beta - kappaOne = gamma) (hgamma : 0 ≤ gamma)
    (htarget : 0 ≤ targetCoefficient) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (candidateBudget48 m beta) +
          targetCoefficient * Real.log (m : ℝ) ^ 2 ≤
        (1 / 1000 : ℝ) *
          (m : ℝ) ^ (gamma + meshDelta) := by
  have hdelta : 0 < meshDelta := by norm_num [meshDelta]
  have hpow :=
    ExternalProposition44.eventually_const_mul_nat_rpow_le
      (2000 * (candidateExponent48 + 11)) gamma
        (gamma + meshDelta) (by linarith)
  have hlogAbsorb := eventually_const_mul_log_sq_le_nat_rpow
    (2000 * (2 + targetCoefficient)) meshDelta hdelta
  filter_upwards [hpow, hlogAbsorb, eventually_ge_atTop 3] with
      m hpowM hlogAbsorbM hm
  have hmR : (1 : ℝ) < m := by
    exact_mod_cast (show 1 < m by omega)
  have hlogOne : 1 < Real.log (m : ℝ) := by
    apply (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < m)).2
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hm)
  have hlog0 : 0 ≤ Real.log (m : ℝ) :=
    (zero_lt_one.trans hlogOne).le
  have hloglog : Real.log (Real.log (m : ℝ)) ≤
      Real.log (m : ℝ) := by
    exact (Real.log_le_sub_one_of_pos (zero_lt_one.trans hlogOne)).trans
      (by linarith)
  have hlogLeSq : Real.log (m : ℝ) ≤ Real.log (m : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hlog0 (sub_nonneg.mpr hlogOne.le)]
  have hpowOne : 1 ≤ (m : ℝ) ^ gamma :=
    Real.one_le_rpow hmR.le hgamma
  have hlogTwelve : Real.log (12 : ℝ) ≤ 11 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 12)
    norm_num at h ⊢
    exact h
  have hbudget := log_candidateBudget48_le hm hbeta hgamma
  have hcoarse :
      Real.log (candidateBudget48 m beta) +
          targetCoefficient * Real.log (m : ℝ) ^ 2 ≤
        (candidateExponent48 + 11) * (m : ℝ) ^ gamma +
          (2 + targetCoefficient) * Real.log (m : ℝ) ^ 2 := by
    calc
      Real.log (candidateBudget48 m beta) +
          targetCoefficient * Real.log (m : ℝ) ^ 2 ≤
          (Real.log 12 + candidateExponent48 * (m : ℝ) ^ gamma +
              2 * Real.log (Real.log (m : ℝ))) +
            targetCoefficient * Real.log (m : ℝ) ^ 2 :=
        add_le_add hbudget le_rfl
      _ ≤ (candidateExponent48 + 11) * (m : ℝ) ^ gamma +
          (2 + targetCoefficient) * Real.log (m : ℝ) ^ 2 := by
        have hll : 2 * Real.log (Real.log (m : ℝ)) ≤
            2 * Real.log (m : ℝ) ^ 2 :=
          (mul_le_mul_of_nonneg_left (hloglog.trans hlogLeSq) (by norm_num))
        nlinarith
  have hpowPart : (candidateExponent48 + 11) * (m : ℝ) ^ gamma ≤
      (1 / 2000 : ℝ) * (m : ℝ) ^ (gamma + meshDelta) := by
    nlinarith
  have hdeltaPow : (m : ℝ) ^ meshDelta ≤
      (m : ℝ) ^ (gamma + meshDelta) := by
    exact Real.rpow_le_rpow_of_exponent_le hmR.le (by linarith)
  have hlogPart : (2 + targetCoefficient) * Real.log (m : ℝ) ^ 2 ≤
      (1 / 2000 : ℝ) * (m : ℝ) ^ (gamma + meshDelta) := by
    have hcoeff : 0 ≤ 2 + targetCoefficient := by linarith
    have hscaled : 2000 *
        ((2 + targetCoefficient) * Real.log (m : ℝ) ^ 2) ≤
        (m : ℝ) ^ (gamma + meshDelta) := by
      calc
        2000 * ((2 + targetCoefficient) * Real.log (m : ℝ) ^ 2) =
            (2000 * (2 + targetCoefficient)) *
              Real.log (m : ℝ) ^ 2 := by ring
        _ ≤ (m : ℝ) ^ meshDelta := hlogAbsorbM
        _ ≤ (m : ℝ) ^ (gamma + meshDelta) := hdeltaPow
    nlinarith
  exact hcoarse.trans (by nlinarith)

/-- The beta-band identity, the mesh escape estimate, and the ceiling return
count combine to give the exact real domination required by the geometric
screen.  The only scale hypothesis is the HLOZ regime in which the first
deficit band lies below `kappaOne`. -/
theorem eventually_adjacent_deficitBand_log_budget_le_escape_returns
    (a : GapScale) (j : ℕ) (targetCoefficient : ℝ)
    (hscale : meshExponent a + meshDelta ≤ kappaOne)
    (htarget : 0 ≤ targetCoefficient) :
    ∀ᶠ m : ℕ in atTop,
      Real.log
          (candidateBudget48 m
            (deficitExponent48 (meshExponent a) (j + 1))) +
          targetCoefficient * Real.log (m : ℝ) ^ 2 ≤
        meshPointEscapeChance m a *
          requiredReturns48 m (deficitExponent48 (meshExponent a) j) := by
  let betaPrev := deficitExponent48 (meshExponent a) j
  let betaNext := deficitExponent48 (meshExponent a) (j + 1)
  let gamma := betaNext - kappaOne
  have hmeshExponentPos : 0 < meshExponent a := by
    unfold meshExponent
    have hindex : (0 : ℝ) < (a : ℕ) + 1 := by positivity
    exact mul_pos hindex (by norm_num [meshDelta])
  have hstep : 0 ≤ kappaOne - meshExponent a - meshDelta := by
    linarith
  have hbetaPrevPos : 0 < betaPrev := by
    dsimp only [betaPrev, deficitExponent48]
    have hj : (0 : ℝ) ≤ j := by positivity
    have hjstep : 0 ≤ (j : ℝ) *
        (kappaOne - meshExponent a - meshDelta) :=
      mul_nonneg hj hstep
    have hdelta : 0 < meshDelta := by norm_num [meshDelta]
    linarith
  have hgamma : 0 ≤ gamma := by
    dsimp only [gamma, betaNext]
    have hkappa := kappaOne_le_deficitExponent48 hscale
      (show 0 < j + 1 by omega)
    linarith
  have hbudget := eventually_log_candidateBudget48_add_log_sq_le
    betaNext gamma targetCoefficient rfl hgamma htarget
  have hreturnPower :=
    (tendsto_nat_rpow_atTop hbetaPrevPos).eventually
      (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hbudget, hreturnPower, eventually_ge_atTop 1] with
      m hbudgetM hreturnPowerM hm
  have hlower :=
    one_div_four_hundred_nat_rpow_sub_le_escape_mul_requiredReturns48
      hm a hreturnPowerM
  have hexponent : betaPrev - meshExponent a = gamma + meshDelta := by
    dsimp only [betaPrev, gamma, betaNext]
    exact deficitExponent48_sub_alpha (meshExponent a) j
  rw [hexponent] at hlower
  have hpowNonneg : 0 ≤ (m : ℝ) ^ (gamma + meshDelta) :=
    Real.rpow_nonneg (by positivity) _
  have hconstant :
      (1 / 1000 : ℝ) * (m : ℝ) ^ (gamma + meshDelta) ≤
        (1 / 400 : ℝ) * (m : ℝ) ^ (gamma + meshDelta) := by
    nlinarith
  exact hbudgetM.trans (hconstant.trans hlower)

/-- ENNReal form of the preceding adjacent-band estimate, ready for the
finite random-clock screen. -/
theorem eventually_candidateBudget48_mul_meshGeometricReturnCost_le_exp_neg
    (a : GapScale) (j : ℕ) (targetCoefficient : ℝ)
    (hscale : meshExponent a + meshDelta ≤ kappaOne)
    (htarget : 0 ≤ targetCoefficient) :
    ∀ᶠ m : ℕ in atTop,
      ((candidateBudget48 m
          (deficitExponent48 (meshExponent a) (j + 1)) : ℕ) : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m a)
            (requiredReturns48 m
              (deficitExponent48 (meshExponent a) j)) ≤
        ENNReal.ofReal
          (Real.exp (-targetCoefficient * Real.log (m : ℝ) ^ 2)) := by
  have hdomination :=
    eventually_adjacent_deficitBand_log_budget_le_escape_returns
      a j targetCoefficient hscale htarget
  filter_upwards [hdomination, eventually_ge_atTop 2] with m hdominationM hm
  simpa only [neg_mul] using
    (candidateBudget48_mul_meshGeometricReturnCost_le_exp_neg
      (show 1 < m by omega) a hdominationM)

/-- A fixed finite multiplicity is absorbed by one of two copies of a
positive `c * log m ^ 2` exponent. -/
theorem eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
    (B : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop,
      (B : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  by_cases hB : B = 0
  · simp [hB]
  have hBpos : 0 < B := Nat.pos_of_ne_zero hB
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hlog.eventually
    (eventually_ge_atTop (max 1 (Real.log (B : ℝ) / c)))
  filter_upwards [hlarge] with m hm
  have hlogOne : 1 ≤ Real.log (m : ℝ) := le_trans (le_max_left _ _) hm
  have hlogRatio : Real.log (B : ℝ) / c ≤ Real.log (m : ℝ) :=
    le_trans (le_max_right _ _) hm
  have hlogB : Real.log (B : ℝ) ≤
      c * Real.log (m : ℝ) := by
    rw [div_le_iff₀ hc] at hlogRatio
    simpa only [mul_comm] using hlogRatio
  have hdominates : Real.log (B : ℝ) +
      c * Real.log (m : ℝ) ^ 2 ≤
        2 * c * Real.log (m : ℝ) ^ 2 := by
    have hcLog : c * Real.log (m : ℝ) ≤
        c * Real.log (m : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg (Real.log (m : ℝ) - 1)]) hc.le
    nlinarith
  simpa only [neg_mul, mul_assoc] using
    (Gap.ennreal_nat_mul_exp_neg_le_exp_neg hBpos hdominates)

/-- Uniform finite-template version of the adjacent-band estimate.  This is
the complete geometric-return part of `hnumeric` for a random-clock screen:
only the lazy and Proposition 4.8 overflow costs remain to be added. -/
theorem eventually_sum_adjacent_deficitBand_geometric_cost_le
    {Band : Type*} (templates : Finset Band)
    (scale : Band → GapScale) (index : Band → ℕ)
    {c : ℝ} (hc : 0 < c)
    (hscale : ∀ band ∈ templates,
      meshExponent (scale band) + meshDelta ≤ kappaOne) :
    ∀ᶠ m : ℕ in atTop,
      ∑ band ∈ templates,
        ((candidateBudget48 m
            (deficitExponent48 (meshExponent (scale band))
              (index band + 1)) : ℕ) : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m (scale band))
            (requiredReturns48 m
              (deficitExponent48 (meshExponent (scale band)) (index band))) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  have heach : ∀ band ∈ templates, ∀ᶠ m : ℕ in atTop,
      ((candidateBudget48 m
          (deficitExponent48 (meshExponent (scale band))
            (index band + 1)) : ℕ) : ℝ≥0∞) *
        Gap.geometricReturnCost (meshPointEscapeChance m (scale band))
          (requiredReturns48 m
            (deficitExponent48 (meshExponent (scale band)) (index band))) ≤
      ENNReal.ofReal
        (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) := by
    intro band hband
    exact eventually_candidateBudget48_mul_meshGeometricReturnCost_le_exp_neg
      (scale band) (index band) (2 * c) (hscale band hband) (by positivity)
  have hall := (Finset.eventually_all templates).2 heach
  have habsorb :=
    eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg templates.card hc
  filter_upwards [hall, habsorb] with m hallM habsorbM
  calc
    ∑ band ∈ templates,
        ((candidateBudget48 m
            (deficitExponent48 (meshExponent (scale band))
              (index band + 1)) : ℕ) : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m (scale band))
            (requiredReturns48 m
              (deficitExponent48 (meshExponent (scale band)) (index band))) ≤
        ∑ _band ∈ templates,
          ENNReal.ofReal
            (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) :=
      Finset.sum_le_sum fun band hband ↦ hallM band hband
    _ = (templates.card : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) := by simp
    _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) :=
      habsorbM

/-- Uniform form for a family of concrete bands whose auxiliary natural
thresholds may depend on `m`.  Only the scale/index projection must lie in a
fixed finite template, and `B` retains multiplicities coming from ranks and
orientations. -/
theorem eventually_sum_dynamic_adjacent_deficitBand_geometric_cost_le
    {Band : Type*}
    (bands : ℕ → Finset Band) (scale : Band → GapScale)
    (index : Band → ℕ) (templates : Finset (GapScale × ℕ)) (B : ℕ)
    {c : ℝ} (hc : 0 < c)
    (hscale : ∀ p ∈ templates,
      meshExponent p.1 + meshDelta ≤ kappaOne)
    (hprojects : ∀ m band, band ∈ bands m →
      (scale band, index band) ∈ templates)
    (hcard : ∀ m, (bands m).card ≤ B) :
    ∀ᶠ m : ℕ in atTop,
      ∑ band ∈ bands m,
        ((candidateBudget48 m
            (deficitExponent48 (meshExponent (scale band))
              (index band + 1)) : ℕ) : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m (scale band))
            (requiredReturns48 m
              (deficitExponent48 (meshExponent (scale band)) (index band))) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  have heach : ∀ p ∈ templates, ∀ᶠ m : ℕ in atTop,
      ((candidateBudget48 m
          (deficitExponent48 (meshExponent p.1) (p.2 + 1)) : ℕ) : ℝ≥0∞) *
        Gap.geometricReturnCost (meshPointEscapeChance m p.1)
          (requiredReturns48 m
            (deficitExponent48 (meshExponent p.1) p.2)) ≤
      ENNReal.ofReal
        (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) := by
    intro p hp
    exact eventually_candidateBudget48_mul_meshGeometricReturnCost_le_exp_neg
      p.1 p.2 (2 * c) (hscale p hp) (by positivity)
  have hall := (Finset.eventually_all templates).2 heach
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg B hc
  filter_upwards [hall, habsorb] with m hallM habsorbM
  let q : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2))
  have hterm : ∀ band ∈ bands m,
      ((candidateBudget48 m
          (deficitExponent48 (meshExponent (scale band))
            (index band + 1)) : ℕ) : ℝ≥0∞) *
        Gap.geometricReturnCost (meshPointEscapeChance m (scale band))
          (requiredReturns48 m
            (deficitExponent48 (meshExponent (scale band)) (index band))) ≤
        q := by
    intro band hband
    exact hallM (scale band, index band) (hprojects m band hband)
  calc
    ∑ band ∈ bands m,
        ((candidateBudget48 m
            (deficitExponent48 (meshExponent (scale band))
              (index band + 1)) : ℕ) : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m (scale band))
            (requiredReturns48 m
              (deficitExponent48 (meshExponent (scale band)) (index band))) ≤
        ∑ _band ∈ bands m, q :=
      Finset.sum_le_sum hterm
    _ = ((bands m).card : ℝ≥0∞) * q := by simp
    _ ≤ (B : ℝ≥0∞) * q := by
      gcongr
      exact_mod_cast hcard m
    _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) :=
      habsorbM

/-- Fully dynamic projection form.  The source index of a concrete band may
depend on the level, because the finite screen stores only the realized band
fields and not the enumeration tag used to construct it. -/
theorem eventually_sum_dynamic_indexed_deficitBand_geometric_cost_le
    {Band : Type*}
    (bands : ℕ → Finset Band) (scale : ℕ → Band → GapScale)
    (index : ℕ → Band → ℕ) (templates : Finset (GapScale × ℕ)) (B : ℕ)
    {c : ℝ} (hc : 0 < c)
    (hscale : ∀ p ∈ templates,
      meshExponent p.1 + meshDelta ≤ kappaOne)
    (hprojects : ∀ m band, band ∈ bands m →
      (scale m band, index m band) ∈ templates)
    (hcard : ∀ m, (bands m).card ≤ B) :
    ∀ᶠ m : ℕ in atTop,
      ∑ band ∈ bands m,
        ((candidateBudget48 m
            (deficitExponent48 (meshExponent (scale m band))
              (index m band + 1)) : ℕ) : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m (scale m band))
            (requiredReturns48 m
              (deficitExponent48 (meshExponent (scale m band))
                (index m band))) ≤
        ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) := by
  have heach : ∀ p ∈ templates, ∀ᶠ m : ℕ in atTop,
      ((candidateBudget48 m
          (deficitExponent48 (meshExponent p.1) (p.2 + 1)) : ℕ) : ℝ≥0∞) *
        Gap.geometricReturnCost (meshPointEscapeChance m p.1)
          (requiredReturns48 m
            (deficitExponent48 (meshExponent p.1) p.2)) ≤
      ENNReal.ofReal
        (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2)) := by
    intro p hp
    exact eventually_candidateBudget48_mul_meshGeometricReturnCost_le_exp_neg
      p.1 p.2 (2 * c) (hscale p hp) (by positivity)
  have hall := (Finset.eventually_all templates).2 heach
  have habsorb := eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg B hc
  filter_upwards [hall, habsorb] with m hallM habsorbM
  let q : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-(2 * c) * Real.log (m : ℝ) ^ 2))
  have hterm : ∀ band ∈ bands m,
      ((candidateBudget48 m
          (deficitExponent48 (meshExponent (scale m band))
            (index m band + 1)) : ℕ) : ℝ≥0∞) *
        Gap.geometricReturnCost (meshPointEscapeChance m (scale m band))
          (requiredReturns48 m
            (deficitExponent48 (meshExponent (scale m band))
              (index m band))) ≤ q := by
    intro band hband
    exact hallM (scale m band, index m band) (hprojects m band hband)
  calc
    ∑ band ∈ bands m,
        ((candidateBudget48 m
            (deficitExponent48 (meshExponent (scale m band))
              (index m band + 1)) : ℕ) : ℝ≥0∞) *
          Gap.geometricReturnCost (meshPointEscapeChance m (scale m band))
            (requiredReturns48 m
              (deficitExponent48 (meshExponent (scale m band))
                (index m band))) ≤
        ∑ _band ∈ bands m, q := Finset.sum_le_sum hterm
    _ = ((bands m).card : ℝ≥0∞) * q := by simp
    _ ≤ (B : ℝ≥0∞) * q := by
      gcongr
      exact_mod_cast hcard m
    _ ≤ ENNReal.ofReal (Real.exp (-c * Real.log (m : ℝ) ^ 2)) :=
      habsorbM

end

end Erdos1165.HLOZGapBetaNumerics
