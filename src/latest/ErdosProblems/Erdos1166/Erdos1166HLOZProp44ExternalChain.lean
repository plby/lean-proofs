/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZExternalChain
import ErdosProblems.Erdos1166.Erdos1166HLOZExternalDeviation
import ErdosProblems.Erdos1166.Erdos1166HLOZExternalDeviationChain
import ErdosProblems.Erdos1166.Erdos1166HLOZNearCriticalBridge

/-!
The source-facing specialization of HLOZ Proposition 4.4 to the iid
terminal-label external chain.  This file also proves the two deterministic
comparisons suppressed by the phrase "for all large `m`" in the paper,
including the harmless upward rounding of the time scale `ψ_m`.
-/

namespace Erdos1166.HLOZProp44ExternalChain

open Filter MeasureTheory Set
open scoped ENNReal

open HLOZExternalUpper
open HLOZExternalChain
open HLOZExternalDeviationChain
open HLOZProp44
open HLOZNearCriticalBridge

@[simp] theorem prop44Psi_eq_nearCriticalHorizon (m : ℕ) :
    prop44Psi m = nearCriticalHorizon m := by
  rfl

theorem prop44RateExponent_eq_horizonExponent :
    prop44RateExponent = horizonExponent := by
  norm_num [prop44RateExponent_eq, horizonExponent_eq]

theorem prop44Beta_eq_lowerTailExponent :
    prop44Beta = lowerTailExponent := by
  norm_num [prop44Beta_eq, lowerTailExponent_eq]

private theorem sqrt_pi_lt_sixteen_ninths :
    Real.sqrt Real.pi < (16 : ℝ) / 9 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 16 / 9)]
  nlinarith [Real.pi_lt_d2]

private theorem eventually_log_prop44Psi_le_sixteen_ninths_sqrt :
    ∀ᶠ m : ℕ in atTop,
      Real.log (prop44Psi m : ℝ) ≤
        (16 / 9 : ℝ) * Real.sqrt (m : ℝ) := by
  let d : ℝ := 16 / 9 - Real.sqrt Real.pi
  have hd : 0 < d := sub_pos.mpr sqrt_pi_lt_sixteen_ninths
  have hc := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := horizonCoefficient) (d := d / 2)
    (p := horizonExponent) (q := 1 / 2)
    horizonCoefficient_pos.le (by positivity)
    (by norm_num [horizonExponent_eq])
  have htwo := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := Real.log 2) (d := d / 2)
    (p := 0) (q := 1 / 2)
    (Real.log_nonneg (by norm_num)) (by positivity) (by norm_num)
  filter_upwards [hc, htwo, eventually_ge_atTop 1] with m hc htwo hm
  have hround := log_horizon_le_nearCriticalLogHorizon_add_log_two m
  rw [prop44Psi_eq_nearCriticalHorizon]
  have hc' : horizonCoefficient * (m : ℝ) ^ horizonExponent ≤
      d / 2 * Real.sqrt (m : ℝ) := by
    simpa only [Real.sqrt_eq_rpow] using hc
  have htwo' : Real.log 2 ≤ d / 2 * Real.sqrt (m : ℝ) := by
    simpa only [Real.rpow_zero, mul_one, Real.sqrt_eq_rpow] using htwo
  dsimp only [d] at hc' htwo'
  calc
    Real.log (nearCriticalHorizon m : ℝ) ≤
        nearCriticalLogHorizon m + Real.log 2 := hround
    _ = Real.sqrt Real.pi * Real.sqrt (m : ℝ) +
          horizonCoefficient * (m : ℝ) ^ horizonExponent +
          Real.log 2 := by rfl
    _ ≤ (16 / 9 : ℝ) * Real.sqrt (m : ℝ) := by linarith

/-- The canonical external-label horizon is eventually much smaller than
the coarse `exp (16 √m)` site budget used in Proposition 4.5.  This is
the deterministic horizon-cardinality comparison implicit in the source. -/
theorem eventually_prop44Psi_le_exp_sixteen_sqrt :
    ∀ᶠ m : ℕ in atTop,
      (prop44Psi m : ℝ) ≤ Real.exp (16 * Real.sqrt (m : ℝ)) := by
  filter_upwards [eventually_log_prop44Psi_le_sixteen_ninths_sqrt]
    with m hlog
  have hpos : 0 < (prop44Psi m : ℝ) := by
    rw [prop44Psi_eq_nearCriticalHorizon]
    exact_mod_cast nearCriticalHorizon_pos m
  calc
    (prop44Psi m : ℝ) = Real.exp (Real.log (prop44Psi m : ℝ)) := by
      rw [Real.exp_log hpos]
    _ ≤ Real.exp ((16 / 9 : ℝ) * Real.sqrt (m : ℝ)) :=
      Real.exp_le_exp.mpr hlog
    _ ≤ Real.exp (16 * Real.sqrt (m : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.sqrt_nonneg (m : ℝ)]

/-- Hence the literal number of labels used by the canonical fixed-depth
partition also fits the Proposition-4.5 site budget. -/
theorem eventually_externalLabelCount_prop44Psi_le_exp_sixteen_sqrt :
    ∀ᶠ m : ℕ in atTop,
      (HLOZExternalUpper.externalLabelCount (prop44Psi m) : ℝ) ≤
        Real.exp (16 * Real.sqrt (m : ℝ)) := by
  filter_upwards [eventually_prop44Psi_le_exp_sixteen_sqrt]
    with m hm
  have hpsi : 0 < prop44Psi m := by
    rw [prop44Psi_eq_nearCriticalHorizon]
    exact nearCriticalHorizon_pos m
  calc
    (HLOZExternalUpper.externalLabelCount (prop44Psi m) : ℝ) ≤
        (prop44Psi m : ℝ) := by
      unfold HLOZExternalUpper.externalLabelCount
      exact_mod_cast (show (prop44Psi m + 1) / 2 ≤ prop44Psi m by omega)
    _ ≤ Real.exp (16 * Real.sqrt (m : ℝ)) := hm

private theorem sqrt_rpow_prop44Beta_sub_one (m : ℕ) :
    Real.sqrt (m : ℝ) ^ (prop44Beta - 1) =
      (m : ℝ) ^ prop44RateExponent := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg m)]
  congr 1
  norm_num [prop44Beta_eq, prop44RateExponent_eq]

/-- The logarithmic comparison used after Markov's inequality in HLOZ
(4.13), with the rounded source horizon. -/
theorem eventually_prop44_log_comparison :
    ∀ᶠ m : ℕ in atTop,
      Real.log 2 +
          8 * Real.log (prop44Psi m : ℝ) ^ (prop44Beta - 1) ≤
        15 * (m : ℝ) ^ prop44RateExponent := by
  have hsmall := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := Real.log 2) (d := (7 : ℝ) / 9)
    (p := 0) (q := prop44RateExponent)
    (Real.log_nonneg (by norm_num)) (by norm_num)
    (by norm_num [prop44RateExponent_eq])
  filter_upwards [eventually_log_prop44Psi_le_sixteen_ninths_sqrt,
      hsmall, eventually_ge_atTop 1]
      with m hlog hsmall hm
  have hlog0 : 0 ≤ Real.log (prop44Psi m : ℝ) :=
    Real.log_natCast_nonneg _
  have hq0 : 0 ≤ prop44Beta - 1 := by
    norm_num [prop44Beta_eq]
  have hpow := Real.rpow_le_rpow hlog0 hlog hq0
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16 / 9)
    (Real.sqrt_nonneg _)] at hpow
  have hconst : (16 / 9 : ℝ) ^ (prop44Beta - 1) ≤ 16 / 9 := by
    apply Real.rpow_le_self_of_one_le (by norm_num)
    norm_num [prop44Beta_eq]
  have hsqrt0 : 0 ≤ Real.sqrt (m : ℝ) ^ (prop44Beta - 1) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hpow' :
      Real.log (prop44Psi m : ℝ) ^ (prop44Beta - 1) ≤
        (16 / 9 : ℝ) * (m : ℝ) ^ prop44RateExponent := by
    calc
      Real.log (prop44Psi m : ℝ) ^ (prop44Beta - 1) ≤
          (16 / 9 : ℝ) ^ (prop44Beta - 1) *
            Real.sqrt (m : ℝ) ^ (prop44Beta - 1) := hpow
      _ ≤ (16 / 9 : ℝ) *
            Real.sqrt (m : ℝ) ^ (prop44Beta - 1) := by gcongr
      _ = (16 / 9 : ℝ) * (m : ℝ) ^ prop44RateExponent := by
        rw [sqrt_rpow_prop44Beta_sub_one]
  have hsmall' : Real.log 2 ≤
      (7 / 9 : ℝ) * (m : ℝ) ^ prop44RateExponent := by
    simpa only [Real.rpow_zero, mul_one] using hsmall
  have hrate0 : 0 ≤ (m : ℝ) ^ prop44RateExponent :=
    Real.rpow_nonneg (Nat.cast_nonneg m) _
  calc
    Real.log 2 +
        8 * Real.log (prop44Psi m : ℝ) ^ (prop44Beta - 1) ≤
      (7 / 9 : ℝ) * (m : ℝ) ^ prop44RateExponent +
        8 * ((16 / 9 : ℝ) * (m : ℝ) ^ prop44RateExponent) :=
      add_le_add hsmall' (mul_le_mul_of_nonneg_left hpow' (by norm_num))
    _ = 15 * (m : ℝ) ^ prop44RateExponent := by ring

private theorem sqrt_pi_lt_two : Real.sqrt Real.pi < 2 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
  nlinarith [Real.pi_lt_four]

private theorem eventually_nearCriticalLogHorizon_le_two_sqrt :
    ∀ᶠ m : ℕ in atTop,
      nearCriticalLogHorizon m ≤ 2 * Real.sqrt (m : ℝ) := by
  let d : ℝ := 2 - Real.sqrt Real.pi
  have hd : 0 < d := sub_pos.mpr sqrt_pi_lt_two
  have hc := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := horizonCoefficient) (d := d)
    (p := horizonExponent) (q := 1 / 2)
    horizonCoefficient_pos.le hd
    (by norm_num [horizonExponent_eq])
  filter_upwards [hc, eventually_ge_atTop 1] with m hc hm
  have hc' : horizonCoefficient * (m : ℝ) ^ horizonExponent ≤
      d * Real.sqrt (m : ℝ) := by
    simpa only [Real.sqrt_eq_rpow] using hc
  dsimp only [d] at hc'
  rw [nearCriticalLogHorizon]
  linarith

private theorem horizonCorrection_sq (m : ℕ) (hm : 0 < m) :
    (horizonCoefficient * (m : ℝ) ^ horizonExponent) ^ 2 =
      horizonCoefficient ^ 2 * (m : ℝ) ^ ((16 : ℝ) / 25) := by
  rw [mul_pow]
  congr 1
  rw [pow_two, ← Real.rpow_add (by exact_mod_cast hm)]
  congr 1
  norm_num [horizonExponent_eq]

private theorem externalLeading_le_one :
    (15 / (16 * Real.pi) : ℝ) ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℝ) < 16 * Real.pi)).2
  nlinarith [Real.pi_gt_three]

private theorem eventually_prop44_threshold_errors :
    ∀ᶠ m : ℕ in atTop,
      (horizonCoefficient * (m : ℝ) ^ horizonExponent) ^ 2 +
          4 * Real.log 2 * Real.sqrt (m : ℝ) +
          Real.log 2 ^ 2 + (m : ℝ) ^ (4 / 5 : ℝ) ≤
        (1 / 8 : ℝ) *
          (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) ^ prop44Beta := by
  have hcorr := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := horizonCoefficient ^ 2) (d := (1 : ℝ) / 32)
    (p := (16 : ℝ) / 25) (q := (41 : ℝ) / 50)
    (sq_nonneg _) (by norm_num) (by norm_num)
  have hround := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := 4 * Real.log 2) (d := (1 : ℝ) / 32)
    (p := (1 : ℝ) / 2) (q := (41 : ℝ) / 50)
    (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
    (by norm_num) (by norm_num)
  have hconst := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := Real.log 2 ^ 2) (d := (1 : ℝ) / 32)
    (p := 0) (q := (41 : ℝ) / 50)
    (sq_nonneg _) (by norm_num) (by norm_num)
  have hsite := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := 1) (d := (1 : ℝ) / 32)
    (p := (4 : ℝ) / 5) (q := (41 : ℝ) / 50)
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hcorr, hround, hconst, hsite,
      eventually_ge_atTop 1]
      with m hcorr hround hconst hsite hm
  have hmpos : 0 < m := by omega
  have hcorr' :
      (horizonCoefficient * (m : ℝ) ^ horizonExponent) ^ 2 ≤
        (1 / 32 : ℝ) * (m : ℝ) ^ ((41 : ℝ) / 50) := by
    rw [horizonCorrection_sq m hmpos]
    exact hcorr
  have hround' :
      4 * Real.log 2 * Real.sqrt (m : ℝ) ≤
        (1 / 32 : ℝ) * (m : ℝ) ^ ((41 : ℝ) / 50) := by
    simpa only [Real.sqrt_eq_rpow, mul_assoc] using hround
  have hconst' : Real.log 2 ^ 2 ≤
      (1 / 32 : ℝ) * (m : ℝ) ^ ((41 : ℝ) / 50) := by
    simpa only [Real.rpow_zero, mul_one] using hconst
  have hsite' : (m : ℝ) ^ (4 / 5 : ℝ) ≤
      (1 / 32 : ℝ) * (m : ℝ) ^ ((41 : ℝ) / 50) := by
    simpa only [one_mul] using hsite
  have hsum :
      (horizonCoefficient * (m : ℝ) ^ horizonExponent) ^ 2 +
          4 * Real.log 2 * Real.sqrt (m : ℝ) +
          Real.log 2 ^ 2 + (m : ℝ) ^ (4 / 5 : ℝ) ≤
        (1 / 8 : ℝ) * (m : ℝ) ^ ((41 : ℝ) / 50) := by
    calc
      _ ≤ (1 / 32 : ℝ) * (m : ℝ) ^ ((41 : ℝ) / 50) +
          (1 / 32 : ℝ) * (m : ℝ) ^ ((41 : ℝ) / 50) +
          (1 / 32 : ℝ) * (m : ℝ) ^ ((41 : ℝ) / 50) +
          (1 / 32 : ℝ) * (m : ℝ) ^ ((41 : ℝ) / 50) :=
        add_le_add (add_le_add (add_le_add hcorr' hround') hconst') hsite'
      _ = (1 / 8 : ℝ) * (m : ℝ) ^ ((41 : ℝ) / 50) := by ring
  have hpiCoeff : 1 ≤ Real.pi ^ ((41 : ℝ) / 50) :=
    Real.one_le_rpow (by linarith [Real.pi_gt_three]) (by norm_num)
  calc
    _ ≤ (1 / 8 : ℝ) * (m : ℝ) ^ ((41 : ℝ) / 50) := hsum
    _ ≤ (1 / 8 : ℝ) *
        (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) ^ prop44Beta := by
      rw [prop44Beta_eq_lowerTailExponent,
        leading_rpow_eq]
      gcongr
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hpiCoeff
          (Real.rpow_nonneg (Nat.cast_nonneg m) ((41 : ℝ) / 50)))

/-- The threshold comparison in HLOZ (4.13).  This proof retains the exact
`15/8 - 2 = -1/8` cross-term cancellation and bounds all ceiling errors by
smaller powers of `m`. -/
theorem eventually_prop44_threshold_comparison :
    ∀ᶠ m : ℕ in atTop,
      lemma25ExternalThreshold (prop44Psi m) ≤
        prop44SiteThreshold m := by
  filter_upwards [eventually_nearCriticalLogHorizon_le_two_sqrt,
      eventually_prop44_threshold_errors, eventually_ge_atTop 1]
      with m hAupper herr hm
  let X : ℝ := Real.sqrt Real.pi * Real.sqrt (m : ℝ)
  let B : ℝ := horizonCoefficient * (m : ℝ) ^ horizonExponent
  let A : ℝ := nearCriticalLogHorizon m
  let L : ℝ := Real.log (prop44Psi m : ℝ)
  let d : ℝ := Real.log 2
  let a : ℝ := 15 / (16 * Real.pi)
  have hmpos : 0 < m := by omega
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg horizonCoefficient_pos.le
      (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  have hAeq : A = X + B := by rfl
  have hA0 : 0 ≤ A := by rw [hAeq]; positivity
  have hd0 : 0 ≤ d := Real.log_nonneg (by norm_num)
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact Real.log_natCast_nonneg _
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := externalLeading_le_one
  have hAle : A ≤ L := by
    dsimp [A, L]
    rw [prop44Psi_eq_nearCriticalHorizon]
    exact nearCriticalLogHorizon_le_log_horizon m
  have hLupper : L ≤ A + d := by
    dsimp [A, L, d]
    rw [prop44Psi_eq_nearCriticalHorizon]
    exact log_horizon_le_nearCriticalLogHorizon_add_log_two m
  have hXleL : X ≤ L := by
    rw [hAeq] at hAle
    linarith
  have hbeta0 : 0 ≤ prop44Beta := by norm_num [prop44Beta_eq]
  have hpowLower : X ^ prop44Beta ≤ L ^ prop44Beta :=
    Real.rpow_le_rpow hX0 hXleL hbeta0
  have hsq : L ^ 2 ≤ (A + d) ^ 2 := by
    exact (sq_le_sq₀ hL0 (add_nonneg hA0 hd0)).2 hLupper
  have hleadSq := pi_inverse_mul_leading_sq m
  change Real.pi⁻¹ * X ^ 2 = (m : ℝ) at hleadSq
  have hcross : Real.pi⁻¹ * (2 * X * B) =
      2 * X ^ prop44Beta := by
    dsimp only [X, B]
    rw [prop44Beta_eq_lowerTailExponent]
    exact horizon_cross_term_eq_two_leading_rpow m hmpos
  have hAexact :
      a * A ^ 2 =
        (15 / 16 : ℝ) * (m : ℝ) +
          (15 / 8 : ℝ) * X ^ prop44Beta + a * B ^ 2 := by
    have haeq : a = (15 / 16 : ℝ) * Real.pi⁻¹ := by
      dsimp [a]
      field_simp [ne_of_gt Real.pi_pos]
    rw [hAeq, haeq]
    calc
      (15 / 16 : ℝ) * Real.pi⁻¹ * (X + B) ^ 2 =
          (15 / 16 : ℝ) *
            (Real.pi⁻¹ * X ^ 2 +
              Real.pi⁻¹ * (2 * X * B) + Real.pi⁻¹ * B ^ 2) := by ring
      _ = (15 / 16 : ℝ) * (m : ℝ) +
          (15 / 8 : ℝ) * X ^ prop44Beta +
            ((15 / 16 : ℝ) * Real.pi⁻¹) * B ^ 2 := by
        rw [hleadSq, hcross]
        ring
  have hroundError :
      a * B ^ 2 + a * (2 * A * d + d ^ 2) +
          (m : ℝ) ^ (4 / 5 : ℝ) ≤
        (1 / 8 : ℝ) * X ^ prop44Beta := by
    have hAupper' : A ≤ 2 * Real.sqrt (m : ℝ) := hAupper
    have hAB : 2 * A * d ≤ 4 * d * Real.sqrt (m : ℝ) := by
      calc
        2 * A * d = (2 * d) * A := by ring
        _ ≤ (2 * d) * (2 * Real.sqrt (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hAupper' (mul_nonneg (by norm_num) hd0)
        _ = 4 * d * Real.sqrt (m : ℝ) := by ring
    have hfirst : a * B ^ 2 ≤ B ^ 2 := by
      exact mul_le_of_le_one_left (sq_nonneg B) ha1
    have hsecond : a * (2 * A * d) ≤
        4 * d * Real.sqrt (m : ℝ) := by
      calc
        a * (2 * A * d) ≤ 2 * A * d :=
          mul_le_of_le_one_left (by positivity) ha1
        _ ≤ 4 * d * Real.sqrt (m : ℝ) := hAB
    have hthird : a * d ^ 2 ≤ d ^ 2 := by
      exact mul_le_of_le_one_left (sq_nonneg d) ha1
    calc
      a * B ^ 2 + a * (2 * A * d + d ^ 2) +
          (m : ℝ) ^ (4 / 5 : ℝ) =
        a * B ^ 2 + a * (2 * A * d) + a * d ^ 2 +
          (m : ℝ) ^ (4 / 5 : ℝ) := by ring
      _ ≤ B ^ 2 + 4 * d * Real.sqrt (m : ℝ) + d ^ 2 +
          (m : ℝ) ^ (4 / 5 : ℝ) := by
        gcongr
      _ ≤ (1 / 8 : ℝ) * X ^ prop44Beta := by
        simpa only [X, B, d] using herr
  dsimp [lemma25ExternalThreshold, prop44SiteThreshold]
  change a * L ^ 2 - 2 * L ^ prop44Beta ≤
    (15 / 16 : ℝ) * (m : ℝ) - (m : ℝ) ^ (4 / 5 : ℝ)
  calc
    a * L ^ 2 - 2 * L ^ prop44Beta ≤
        a * (A + d) ^ 2 - 2 * X ^ prop44Beta := by
      exact sub_le_sub
        (mul_le_mul_of_nonneg_left hsq ha0)
        (mul_le_mul_of_nonneg_left hpowLower (by norm_num))
    _ = (15 / 16 : ℝ) * (m : ℝ) -
          (1 / 8 : ℝ) * X ^ prop44Beta +
          (a * B ^ 2 + a * (2 * A * d + d ^ 2)) := by
      rw [show (A + d) ^ 2 = A ^ 2 + (2 * A * d + d ^ 2) by ring,
        mul_add, hAexact]
      ring
    _ ≤ (15 / 16 : ℝ) * (m : ℝ) -
          (m : ℝ) ^ (4 / 5 : ℝ) := by
      linarith

theorem lemma25ExternalThreshold_eq_externalThreshold (n : ℕ) :
    lemma25ExternalThreshold n = externalThreshold n := by
  unfold lemma25ExternalThreshold externalThreshold
  rw [prop44Beta_eq, beta_eq]

theorem lemma25ExternalTail_eq_externalRate (n : ℕ) :
    lemma25ExternalTail n = externalRate n := by
  unfold lemma25ExternalTail externalRate
  rw [prop44Beta_eq, rateExponent_eq]
  norm_num
  ring

theorem tendsto_prop44Psi : Tendsto prop44Psi atTop atTop := by
  rw [show prop44Psi = nearCriticalHorizon by funext m; simp]
  apply tendsto_atTop.2
  intro N
  have hsqrt : Tendsto (fun m : ℕ ↦ Real.sqrt (m : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hcoeff : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hleading : Tendsto
      (fun m : ℕ ↦ Real.sqrt Real.pi * Real.sqrt (m : ℝ)) atTop atTop :=
    hsqrt.const_mul_atTop hcoeff
  filter_upwards [hleading.eventually (eventually_ge_atTop (N : ℝ))]
      with m hm
  have hcorrection : 0 ≤
      horizonCoefficient * (m : ℝ) ^ horizonExponent :=
    mul_nonneg horizonCoefficient_pos.le
      (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  have hlog : (N : ℝ) ≤ nearCriticalLogHorizon m := by
    rw [nearCriticalLogHorizon]
    linarith
  have hexp : nearCriticalLogHorizon m ≤
      Real.exp (nearCriticalLogHorizon m) := by
    linarith [Real.add_one_le_exp (nearCriticalLogHorizon m)]
  have hceil : Real.exp (nearCriticalLogHorizon m) ≤
      (nearCriticalHorizon m : ℝ) := Nat.le_ceil _
  exact_mod_cast hlog.trans (hexp.trans hceil)

/-- Convert the real-valued external-chain deviation estimate to the ENNReal
one-site premise consumed by the Proposition 4.4 counting argument. -/
theorem eventually_externalPathLaw_lemma25_tail_of_chain_deviation
    (hdev : HasExternalChainUpperDeviation) :
    ∀ᶠ n : ℕ in atTop,
      externalPathLaw {s |
          lemma25ExternalThreshold n ≤
            (localTime s n (0, 0) : ℝ)} ≤
        ENNReal.ofReal (lemma25ExternalTail n) := by
  filter_upwards [hdev] with n hn
  rw [lemma25ExternalThreshold_eq_externalThreshold,
    externalPathLaw_highLocalTime_eq_externalChainUpperBad]
  rw [← ENNReal.ofReal_toReal
    (measure_ne_top incrementLaw (externalChainUpperBad n))]
  apply ENNReal.ofReal_le_ofReal
  rw [lemma25ExternalTail_eq_externalRate]
  exact hn

/-- HLOZ Proposition 4.4, equation (4.13), for the actual iid external
terminal-label chain.  All deterministic comparisons, stationarity, parity,
and the exact law transfer have been discharged; the only premise is the
fixed-origin deviation conclusion of Lemma 2.5(2). -/
theorem eventually_prop44_many_even_sites_bound_of_chain_deviation
    (hdev : HasExternalChainUpperDeviation) :
    ∀ᶠ m : ℕ in atTop,
      externalPathLaw {s |
          Real.exp (16 * (m : ℝ) ^ prop44RateExponent) <
            ((evenSitesAtLeastReal s (prop44Psi m)
              (prop44SiteThreshold m)).card : ℝ)} ≤
        ENNReal.ofReal
          (Real.exp (-(m : ℝ) ^ prop44RateExponent)) := by
  have htail := tendsto_prop44Psi.eventually
    (eventually_externalPathLaw_lemma25_tail_of_chain_deviation hdev)
  filter_upwards [eventually_prop44_threshold_comparison,
      eventually_prop44_log_comparison, htail]
      with m hthreshold hlog htail
  exact prop44_many_even_sites_bound_of_lemma25
    externalPathLaw externalPathLaw_hasStationaryEvenIncrements
    externalPathLaw_evenSitesAtEvenTimes m hthreshold hlog htail

/-- Proposition 4.4 with the remaining probabilistic hypotheses expanded to
the exact fixed-origin collision kernel and sharp external Green estimate. -/
theorem eventually_prop44_many_even_sites_bound_of_kernel_and_sharpGreen
    (hKernel : HasExternalFixedOriginKernel)
    (hGreen : HasExternalSharpGreenUpper) :
    ∀ᶠ m : ℕ in atTop,
      externalPathLaw {s |
          Real.exp (16 * (m : ℝ) ^ prop44RateExponent) <
            ((evenSitesAtLeastReal s (prop44Psi m)
              (prop44SiteThreshold m)).card : ℝ)} ≤
        ENNReal.ofReal
          (Real.exp (-(m : ℝ) ^ prop44RateExponent)) :=
  eventually_prop44_many_even_sites_bound_of_chain_deviation
    (hasExternalChainUpperDeviation_of_kernel_and_sharpGreen hKernel hGreen)

end Erdos1166.HLOZProp44ExternalChain
