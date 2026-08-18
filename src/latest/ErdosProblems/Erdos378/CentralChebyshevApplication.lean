/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.InverseSquareChebyshevApplication

/-!
# Uniform application of the central reciprocal Chebyshev estimate

The reciprocal phases in Granville--Ramaré's high-index argument have
frequency anywhere between the square and the sixteenth power of the prime
scale.  This file packages the finite central Vaughan estimate uniformly over
that entire range.
-/

open Filter
open scoped Topology

namespace Erdos378
namespace CentralChebyshevApplication

open AdaptiveShifts
open CentralAsymptotic
open CentralChebyshev
open CentralCorrelation
open CentralVaughanFourth
open PrimeReciprocal
open InverseSquareChebyshevAsymptotic
open InverseSquareChebyshevRate
open InverseSquareChebyshevApplication
open InverseSquareAdaptiveShifts
open ReciprocalChebyshevAsymptotic
open BoundedGaps.Maynard

noncomputable section

def centralUniformDelta (y : ℕ) : ℝ :=
  34 / logarithmicSafety (inverseSquareUniformScale y) +
    8 * (inverseSquareUniformMoment y (inverseSquareUniformScale y)
      (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹

lemma centralUniformDelta_nonneg (y : ℕ) : 0 ≤ centralUniformDelta y := by
  unfold centralUniformDelta
  have hM : 0 ≤ inverseSquareUniformMoment y (inverseSquareUniformScale y)
      (inverseSquareCorrelationCap y) :=
    inverseSquareUniformMoment_nonneg (by unfold inverseSquareUniformScale; omega)
  exact add_nonneg (div_nonneg (by norm_num) (by
    unfold logarithmicSafety
    positivity [Real.log_natCast_nonneg]))
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hM _))

lemma adaptiveMomentEnvelope_le_uniform
    {M y : ℕ} (hZ : inverseSquareUniformScale y ≤ M) (hMy : M ≤ y) :
    adaptiveMomentEnvelope M ≤
      inverseSquareUniformMoment y (inverseSquareUniformScale y)
        (inverseSquareCorrelationCap y) := by
  let Z := inverseSquareUniformScale y
  have hZpos : 1 ≤ Z := by dsimp only [Z, inverseSquareUniformScale]; omega
  have hMpos : 1 ≤ M := hZpos.trans hZ
  have hbZ : 0 < baseShift Z := baseShift_pos (Nat.zero_lt_of_lt hZpos)
  have hbM : 0 < baseShift M := baseShift_pos (Nat.zero_lt_of_lt hMpos)
  have hb : baseShift Z ≤ baseShift M :=
    InverseSquareChebyshevAsymptotic.monotone_baseShift hZ
  have hS : logarithmicSafety M ≤ logarithmicSafety y :=
    logarithmicSafety_mono hMpos hMy
  have hSM : 0 ≤ logarithmicSafety M := (logarithmicSafety_pos hMpos).le
  have hSY : 0 ≤ logarithmicSafety y :=
    (logarithmicSafety_pos (hMpos.trans hMy)).le
  have hfirst : 32 / (baseShift M : ℝ) ≤ 32 / (baseShift Z : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hbZ)
      (by exact_mod_cast hb)
  have hsecond : 1 / (256 * (baseShift M : ℝ)) ≤
      1 / (256 * (baseShift Z : ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num)
      (mul_pos (by norm_num) (by exact_mod_cast hbZ))
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hb) (by norm_num))
  have hterminal : terminalSafetyConstant * logarithmicSafety M ^ 64 /
        (32 * (baseShift M : ℝ)) ≤
      inverseSquareTerminalConstant * logarithmicSafety y ^ 64 /
        (32 * (baseShift Z : ℝ)) := by
    have hconst : terminalSafetyConstant ≤ inverseSquareTerminalConstant := by
      unfold terminalSafetyConstant inverseSquareTerminalConstant
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 63 ≤ 64))
        (by norm_num)
    have hnum : terminalSafetyConstant * logarithmicSafety M ^ 64 ≤
        inverseSquareTerminalConstant * logarithmicSafety y ^ 64 := by
      exact mul_le_mul hconst (pow_le_pow_left₀ hSM hS 64)
        (pow_nonneg hSM 64) inverseSquareTerminalConstant_pos.le
    have hden : (0 : ℝ) < 32 * baseShift Z :=
      mul_pos (by norm_num) (by exact_mod_cast hbZ)
    calc
      _ ≤ terminalSafetyConstant * logarithmicSafety M ^ 64 /
          (32 * (baseShift Z : ℝ)) :=
        div_le_div_of_nonneg_left
          (mul_nonneg terminalSafetyConstant_pos.le (pow_nonneg hSM 64))
          hden (by exact_mod_cast Nat.mul_le_mul_left 32 hb)
      _ ≤ _ := div_le_div_of_nonneg_right hnum hden.le
  unfold adaptiveMomentEnvelope inverseSquareUniformMoment
  apply mul_le_mul_of_nonneg_left _
    (HigherDerivative.vdcMomentConstant_pos 32).le
  have hactive : 0 ≤
      (12 * 2 ^ 35 * (2 * (inverseSquareCorrelationCap y : ℝ)) ^ 33) *
        (logarithmicSafety y ^ 32 / (Z : ℝ)) := by
    apply mul_nonneg
    · exact mul_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 35))
        (pow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) 33)
    · exact div_nonneg (pow_nonneg hSY 32) (Nat.cast_nonneg _)
  exact (add_le_add (add_le_add hfirst hsecond) hterminal).trans
    (le_add_of_nonneg_right hactive)

lemma adaptiveCorrelationEnvelope_le_uniform
    {M y : ℕ} (hZ : inverseSquareUniformScale y ≤ M) (hMy : M ≤ y) :
    adaptiveCorrelationEnvelope M ≤ centralUniformDelta y * M := by
  have hMpos : 1 ≤ M := by
    exact (show 1 ≤ inverseSquareUniformScale y by
      unfold inverseSquareUniformScale; omega).trans hZ
  have hmoment := adaptiveMomentEnvelope_le_uniform hZ hMy
  have hmoment0 := adaptiveMomentEnvelope_nonneg hMpos
  have hrpow := Real.rpow_le_rpow hmoment0 hmoment
    (by norm_num : (0 : ℝ) ≤ ((2 ^ 32 : ℕ) : ℝ)⁻¹)
  have hsafe : logarithmicSafety (inverseSquareUniformScale y) ≤
      logarithmicSafety M :=
    logarithmicSafety_mono (by unfold inverseSquareUniformScale; omega) hZ
  have hsafePos : 0 < logarithmicSafety (inverseSquareUniformScale y) :=
    logarithmicSafety_pos (by unfold inverseSquareUniformScale; omega)
  have hfirst : 34 / logarithmicSafety M ≤
      34 / logarithmicSafety (inverseSquareUniformScale y) :=
    div_le_div_of_nonneg_left (by norm_num) hsafePos hsafe
  have hMR : 0 ≤ (M : ℝ) := by positivity
  unfold adaptiveCorrelationEnvelope centralUniformDelta
  calc
    34 * (M : ℝ) / logarithmicSafety M +
        8 * (M : ℝ) * adaptiveMomentEnvelope M ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹ =
      (34 / logarithmicSafety M +
        8 * adaptiveMomentEnvelope M ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹) * M := by ring
    _ ≤ (34 / logarithmicSafety (inverseSquareUniformScale y) +
        8 * (inverseSquareUniformMoment y (inverseSquareUniformScale y)
          (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹) * M := by
      apply mul_le_mul_of_nonneg_right _ hMR
      exact add_le_add hfirst (mul_le_mul_of_nonneg_left hrpow (by norm_num))
    _ = _ := by ring

private theorem tendsto_log_pow_div_uniformSafety_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 33 /
      logarithmicSafety (inverseSquareUniformScale y)) atTop (nhds 0) := by
  let Z : ℕ → ℕ := inverseSquareUniformScale
  have hZTop : Tendsto Z atTop atTop := tendsto_inverseSquareUniformScale_atTop
  have hlogTop : Tendsto (fun y : ℕ ↦ Real.log (Z y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hZTop)
  have hpowTop : Tendsto (fun y : ℕ ↦ Real.log (Z y : ℝ) ^ 67)
      atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : 67 ≠ 0)).comp hlogTop
  have hupper : Tendsto (fun y : ℕ ↦
      (16 : ℝ) ^ 33 / Real.log (Z y : ℝ) ^ 67) atTop (nhds 0) := by
    have hinv := hpowTop.inv_tendsto_atTop
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply, Function.comp_apply] using
      hinv.const_mul ((16 : ℝ) ^ 33)
  have hnonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ Real.log (y : ℝ) ^ 33 / logarithmicSafety (Z y) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    exact div_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 33)
      (by unfold logarithmicSafety; positivity)
  have hbound : ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ^ 33 / logarithmicSafety (Z y) ≤
        (16 : ℝ) ^ 33 / Real.log (Z y : ℝ) ^ 67 := by
    filter_upwards [eventually_ge_atTop 4,
      hZTop.eventually (eventually_ge_atTop 3)] with y hy hZ
    let G : ℝ := Real.log (y : ℝ)
    let H : ℝ := Real.log (Z y : ℝ)
    have hG : 0 ≤ G := by
      dsimp only [G]
      exact Real.log_natCast_nonneg y
    have hH : 0 < H := by
      dsimp only [H]
      exact Real.log_pos (by exact_mod_cast (show 1 < Z y by omega))
    have hyZ : y < (Z y) ^ 16 := by
      simpa only [Z, inverseSquareUniformScale] using
        lt_baseShift_succ_pow_sixteen y
    have hlog : G ≤ 16 * H := by
      have hcast : (y : ℝ) ≤ ((Z y : ℕ) : ℝ) ^ 16 := by
        exact_mod_cast hyZ.le
      have h := Real.log_le_log (by positivity : (0 : ℝ) < y) hcast
      rw [Real.log_pow] at h
      simpa only [G, H, Nat.cast_ofNat] using h
    have hnum : G ^ 33 ≤ (16 : ℝ) ^ 33 * H ^ 33 := by
      calc
        G ^ 33 ≤ (16 * H) ^ 33 := pow_le_pow_left₀ hG hlog 33
        _ = (16 : ℝ) ^ 33 * H ^ 33 := by rw [mul_pow]
    have hden : H ^ 100 ≤ logarithmicSafety (Z y) := by
      unfold logarithmicSafety
      exact pow_le_pow_left₀ hH.le (by linarith) 100
    calc
      G ^ 33 / logarithmicSafety (Z y) ≤ G ^ 33 / H ^ 100 :=
        div_le_div_of_nonneg_left (pow_nonneg hG 33) (pow_pos hH 100) hden
      _ ≤ ((16 : ℝ) ^ 33 * H ^ 33) / H ^ 100 :=
        div_le_div_of_nonneg_right hnum (pow_nonneg hH.le 100)
      _ = (16 : ℝ) ^ 33 / H ^ 67 := by field_simp [hH.ne']
  simpa only [Z] using squeeze_zero' hnonneg hbound hupper

private theorem tendsto_log_pow_mul_uniformMoment_rpow_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 33 *
      (8 * (inverseSquareUniformMoment y (inverseSquareUniformScale y)
        (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹))
      atTop (nhds 0) := by
  have hr : 0 < inverseSquarePowerRate / 2 := by
    have := inverseSquarePowerRate_pos
    linarith
  have hupper : Tendsto (fun y : ℕ ↦
      8 * (y : ℝ) ^ (-(inverseSquarePowerRate / 2))) atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      (((tendsto_rpow_neg_atTop hr).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 8)
  have hsafety := eventually_logarithmicSafety_pow_le_rpow 1 hr
  have hnonneg : ∀ᶠ y : ℕ in atTop, 0 ≤ Real.log (y : ℝ) ^ 33 *
      (8 * (inverseSquareUniformMoment y (inverseSquareUniformScale y)
        (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    have hm := inverseSquareUniformMoment_nonneg (y := y)
      (C := inverseSquareCorrelationCap y)
      (show 1 ≤ inverseSquareUniformScale y by unfold inverseSquareUniformScale; omega)
    positivity
  have hbound : ∀ᶠ y : ℕ in atTop, Real.log (y : ℝ) ^ 33 *
      (8 * (inverseSquareUniformMoment y (inverseSquareUniformScale y)
        (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹) ≤
        8 * (y : ℝ) ^ (-(inverseSquarePowerRate / 2)) := by
    filter_upwards [eventually_ge_atTop 1, hsafety,
      eventually_inverseSquareUniformMoment_rpow_le_rate] with y hy hs hm
    have hyR : (0 : ℝ) < y := by positivity
    have hlogSafety : Real.log (y : ℝ) ^ 33 ≤ logarithmicSafety y := by
      unfold logarithmicSafety
      have hlog0 := Real.log_natCast_nonneg y
      have hbase : (1 : ℝ) ≤ Real.log (y : ℝ) + 2 := by linarith
      exact (pow_le_pow_left₀ hlog0 (by linarith) 33).trans
        (pow_le_pow_right₀ hbase (by omega))
    have hm0 : 0 ≤
        (inverseSquareUniformMoment y (inverseSquareUniformScale y)
          (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹ :=
      Real.rpow_nonneg (inverseSquareUniformMoment_nonneg
        (show 1 ≤ inverseSquareUniformScale y by
          unfold inverseSquareUniformScale; omega)) _
    calc
      _ = 8 * (Real.log (y : ℝ) ^ 33 *
          (inverseSquareUniformMoment y (inverseSquareUniformScale y)
            (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹) := by ring
      _ ≤ 8 * (logarithmicSafety y *
          (inverseSquareUniformMoment y (inverseSquareUniformScale y)
            (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hlogSafety hm0) (by norm_num)
      _ ≤ 8 * ((y : ℝ) ^ (inverseSquarePowerRate / 2) *
          (y : ℝ) ^ (-inverseSquarePowerRate)) := by
        have hs' : logarithmicSafety y ≤
            (y : ℝ) ^ (inverseSquarePowerRate / 2) := by simpa using hs
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul hs' hm hm0 (Real.rpow_nonneg (by positivity) _)
      _ = 8 * (y : ℝ) ^ (-(inverseSquarePowerRate / 2)) := by
        rw [← Real.rpow_add hyR]
        congr 2
        ring
  exact squeeze_zero' hnonneg hbound hupper

theorem tendsto_log_pow_mul_centralUniformDelta_zero :
    Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 33 * centralUniformDelta y) atTop (nhds 0) := by
  have hfirst := tendsto_log_pow_div_uniformSafety_zero.const_mul 34
  have hsecond := tendsto_log_pow_mul_uniformMoment_rpow_zero
  unfold centralUniformDelta
  convert hfirst.add hsecond using 1
  · funext y
    ring
  · norm_num

def centralTypeBound (y : ℕ) : ℝ :=
  1 + centralUniformDelta y * y

lemma centralTypeBound_nonneg (y : ℕ) : 0 ≤ centralTypeBound y := by
  unfold centralTypeBound
  exact add_nonneg (by norm_num)
    (mul_nonneg (centralUniformDelta_nonneg y) (Nat.cast_nonneg _))

theorem tendsto_log_pow_mul_centralTypeBound_div_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 33 *
      (centralTypeBound y / (y : ℝ))) atTop (nhds 0) := by
  have hfirst : Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 33 / (y : ℝ)) atTop (nhds 0) := by
    have h := tendsto_log_natCast_rpow_div_rpow (33 : ℝ) 1 (by norm_num)
    simpa only [Real.rpow_one,
      show (33 : ℝ) = ((33 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] using h
  have hsecond := tendsto_log_pow_mul_centralUniformDelta_zero
  unfold centralTypeBound
  convert hfirst.add hsecond using 1
  · funext y
    by_cases hy : y = 0
    · simp [hy]
    field_simp
  · norm_num

def centralFourthError (y : ℕ) : ℝ :=
  2 / (reciprocalVaughanCutoff y : ℝ) + centralUniformDelta y

lemma centralFourthError_nonneg (y : ℕ) : 0 ≤ centralFourthError y := by
  unfold centralFourthError
  exact add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _))
    (centralUniformDelta_nonneg y)

private theorem tendsto_log_eight_mul_cutoff_inverse_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 8 *
      (2 / (reciprocalVaughanCutoff y : ℝ))) atTop (nhds 0) := by
  have hlogTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpowTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 8)
      atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : 8 ≠ 0)).comp hlogTop
  have hupper : Tendsto (fun y : ℕ ↦
      2 / Real.log (y : ℝ) ^ 8) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply, Function.comp_apply] using
      hpowTop.inv_tendsto_atTop.const_mul 2
  have hnonneg : ∀ᶠ y : ℕ in atTop, 0 ≤ Real.log (y : ℝ) ^ 8 *
      (2 / (reciprocalVaughanCutoff y : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 8)
      (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hbound : ∀ᶠ y : ℕ in atTop, Real.log (y : ℝ) ^ 8 *
      (2 / (reciprocalVaughanCutoff y : ℝ)) ≤
        2 / Real.log (y : ℝ) ^ 8 := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    let G : ℝ := Real.log (y : ℝ)
    let T : ℝ := reciprocalVaughanCutoff y
    have hG : (1 : ℝ) ≤ G := by simpa only [G] using one_le_log_natCast hy
    have hGpos : 0 < G := by dsimp only [G]; linarith
    have hT : G ^ 16 < T := by
      simpa only [G, T] using (reciprocalVaughanCutoff_real_bounds hy).1
    have hdiv : G ^ 8 / T ≤ G ^ 8 / G ^ 16 :=
      div_le_div_of_nonneg_left (pow_nonneg hGpos.le 8) (pow_pos hGpos 16) hT.le
    change G ^ 8 * (2 / T) ≤ 2 / G ^ 8
    calc
      _ = 2 * (G ^ 8 / T) := by ring
      _ ≤ 2 * (G ^ 8 / G ^ 16) := by gcongr
      _ = 2 / G ^ 8 := by field_simp [hGpos.ne']
  exact squeeze_zero' hnonneg hbound hupper

private theorem tendsto_log_eight_mul_delta_zero :
    Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 8 * centralUniformDelta y) atTop (nhds 0) := by
  have hnonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ Real.log (y : ℝ) ^ 8 * centralUniformDelta y := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 8)
      (centralUniformDelta_nonneg y)
  have hbound : ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ^ 8 * centralUniformDelta y ≤
        Real.log (y : ℝ) ^ 33 * centralUniformDelta y := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (one_le_log_natCast hy) (by omega))
      (centralUniformDelta_nonneg y)
  exact squeeze_zero' hnonneg hbound
    tendsto_log_pow_mul_centralUniformDelta_zero

theorem tendsto_log_eight_mul_centralFourthError_zero :
    Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 8 * centralFourthError y) atTop (nhds 0) := by
  unfold centralFourthError
  convert tendsto_log_eight_mul_cutoff_inverse_zero.add
    tendsto_log_eight_mul_delta_zero using 1
  · funext y
    ring
  · norm_num

def centralFourthLimitConstant : ℝ := 16 * Real.sqrt 5000

lemma centralFourthLimitConstant_nonneg : 0 ≤ centralFourthLimitConstant := by
  unfold centralFourthLimitConstant
  positivity

lemma central_fourth_term_div_le {y : ℕ} (hy : 4 ≤ y) :
    ((dyadicExponentRange y).card : ℝ) ^ 2 *
        Real.sqrt (centralFourthUniformMajorant y
          (reciprocalVaughanCutoff y) (centralUniformDelta y)) / (y : ℝ) ≤
      centralFourthLimitConstant *
        Real.sqrt (Real.log (y : ℝ) ^ 8 * centralFourthError y) := by
  let Y : ℝ := y
  let G : ℝ := Real.log Y
  let T : ℝ := reciprocalVaughanCutoff y
  let E : ℝ := centralFourthError y
  let D : ℝ := Real.sqrt 5000
  have hY : 0 < Y := by positivity
  have hG : 1 ≤ G := by simpa only [G, Y] using one_le_log_natCast hy
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hT : 0 < T := by
    change (0 : ℝ) < (reciprocalVaughanCutoff y : ℝ)
    exact_mod_cast reciprocalVaughanCutoff_pos y
  have hE : 0 ≤ E := by simpa only [E] using centralFourthError_nonneg y
  have hlogTwo : Real.log (2 * Y) ≤ 2 * G := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hY.ne']
    have hlog2 : Real.log 2 ≤ G :=
      Real.log_le_log (by norm_num) (by
        change (2 : ℝ) ≤ (y : ℝ)
        exact_mod_cast (show 2 ≤ y by omega))
    linarith
  have hlogT : Real.log T + 3 ≤ 20 * G := by
    have hbase := log_reciprocalVaughanCutoff_le hy
    change Real.log T ≤ 17 * G at hbase
    linarith [hG]
  have hlogTwo0 : 0 ≤ Real.log (2 * Y) :=
    Real.log_nonneg (by
      have hYone : (1 : ℝ) ≤ Y := by
        change (1 : ℝ) ≤ (y : ℝ)
        exact_mod_cast (show 1 ≤ y by omega)
      nlinarith)
  have hlogT0 : 0 ≤ Real.log T + 3 := by
    have hTone : (1 : ℝ) ≤ T := by
      change (1 : ℝ) ≤ (reciprocalVaughanCutoff y : ℝ)
      exact_mod_cast reciprocalVaughanCutoff_pos y
    have : 0 ≤ Real.log T := Real.log_nonneg hTone
    linarith
  have hA : centralFourthUniformMajorant y (reciprocalVaughanCutoff y)
      (centralUniformDelta y) ≤ 5000 * Y ^ 2 * G ^ 4 * E := by
    unfold centralFourthUniformMajorant
    change (8 / 3 : ℝ) * Y ^ 2 * Real.log (2 * Y) ^ 2 *
      (Real.log T + 3) ^ 2 * E ≤ _
    calc
      _ ≤ (8 / 3 : ℝ) * Y ^ 2 * (2 * G) ^ 2 * (20 * G) ^ 2 * E := by
        gcongr
      _ = (12800 / 3 : ℝ) * Y ^ 2 * G ^ 4 * E := by ring
      _ ≤ 5000 * Y ^ 2 * G ^ 4 * E := by
        have hrest : 0 ≤ Y ^ 2 * G ^ 4 * E := by positivity
        rw [show (12800 / 3 : ℝ) * Y ^ 2 * G ^ 4 * E =
            (12800 / 3 : ℝ) * (Y ^ 2 * G ^ 4 * E) by ring,
          show (5000 : ℝ) * Y ^ 2 * G ^ 4 * E =
            5000 * (Y ^ 2 * G ^ 4 * E) by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) hrest
  have hDsq : D ^ 2 = 5000 := by
    dsimp only [D]
    rw [Real.sq_sqrt]
    norm_num
  have hsqrtA : Real.sqrt (centralFourthUniformMajorant y
      (reciprocalVaughanCutoff y) (centralUniformDelta y)) ≤
      D * Y * G ^ 2 * Real.sqrt E := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    calc
      _ ≤ 5000 * Y ^ 2 * G ^ 4 * E := hA
      _ = (D * Y * G ^ 2 * Real.sqrt E) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, hDsq, Real.sq_sqrt hE]
        ring
  have hcard := card_dyadicExponentRange_le_four_log hy
  change ((dyadicExponentRange y).card : ℝ) ≤ 4 * G at hcard
  have hcardSq : ((dyadicExponentRange y).card : ℝ) ^ 2 ≤ 16 * G ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (dyadicExponentRange y).card by positivity]
  change ((dyadicExponentRange y).card : ℝ) ^ 2 *
      Real.sqrt (centralFourthUniformMajorant y
        (reciprocalVaughanCutoff y) (centralUniformDelta y)) / Y ≤
    16 * D * Real.sqrt (G ^ 8 * E)
  calc
    _ ≤ (16 * G ^ 2) * (D * Y * G ^ 2 * Real.sqrt E) / Y := by gcongr
    _ = 16 * D * G ^ 4 * Real.sqrt E := by field_simp
    _ = 16 * D * Real.sqrt (G ^ 8 * E) := by
      have hsqrtG : Real.sqrt (G ^ 8) = G ^ 4 := by
        rw [show G ^ 8 = (G ^ 4) ^ 2 by ring,
          Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hG0 4)]
      rw [Real.sqrt_mul (pow_nonneg hG0 8), hsqrtG]
      ring

theorem tendsto_centralChebyshevMajorant_div_zero :
    Tendsto (fun y : ℕ ↦ centralChebyshevMajorant y
      (reciprocalVaughanCutoff y) (centralTypeBound y)
      (centralUniformDelta y) / (y : ℝ)) atTop (nhds 0) := by
  let A : ℕ → ℝ := fun y ↦ Real.log (y : ℝ) ^ 33 *
    (centralTypeBound y / (y : ℝ))
  let B : ℕ → ℝ := fun y ↦ centralFourthLimitConstant *
    Real.sqrt (Real.log (y : ℝ) ^ 8 * centralFourthError y)
  have hA : Tendsto A atTop (nhds 0) :=
    tendsto_log_pow_mul_centralTypeBound_div_zero
  have hB : Tendsto B atTop (nhds 0) := by
    have hsqrt := tendsto_log_eight_mul_centralFourthError_zero.sqrt
    simpa only [B, Real.sqrt_zero, mul_zero] using
      hsqrt.const_mul centralFourthLimitConstant
  have hnonneg : ∀ y : ℕ, 0 ≤ centralChebyshevMajorant y
      (reciprocalVaughanCutoff y) (centralTypeBound y)
        (centralUniformDelta y) / (y : ℝ) := by
    intro y
    exact div_nonneg (by
      unfold centralChebyshevMajorant
      exact add_nonneg (add_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
          (mul_nonneg (by norm_num) (Real.log_natCast_nonneg y))
          (centralTypeBound_nonneg y)))
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
          (Real.log_natCast_nonneg y) (centralTypeBound_nonneg y))))
        (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)))
      (Nat.cast_nonneg _)
  have hbound : ∀ᶠ y : ℕ in atTop,
      centralChebyshevMajorant y (reciprocalVaughanCutoff y)
          (centralTypeBound y) (centralUniformDelta y) / (y : ℝ) ≤
        8 * A y + B y := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    let G : ℝ := Real.log (y : ℝ)
    let T : ℝ := reciprocalVaughanCutoff y
    let U : ℝ := centralTypeBound y / (y : ℝ)
    have hG : 1 ≤ G := by simpa only [G] using one_le_log_natCast hy
    have hT : T ≤ 2 * G ^ 16 := by
      have hb := (reciprocalVaughanCutoff_real_bounds hy).2
      have hpow : (1 : ℝ) ≤ G ^ 16 := one_le_pow₀ hG
      change T ≤ 2 * G ^ 16
      calc
        T ≤ G ^ 16 + 1 := by simpa only [T, G] using hb
        _ ≤ 2 * G ^ 16 := by linarith
    have hU : 0 ≤ U := div_nonneg (centralTypeBound_nonneg y) (Nat.cast_nonneg _)
    have hsmall : (T * (2 * G * centralTypeBound y) +
          T ^ 2 * (G * centralTypeBound y)) / (y : ℝ) ≤ 8 * A y := by
      have hT0 : 0 ≤ T := by positivity
      have hfirst : T * (2 * G) * U ≤ 4 * G ^ 17 * U := by
        calc
          _ ≤ (2 * G ^ 16) * (2 * G) * U := by gcongr
          _ = 4 * G ^ 17 * U := by ring
      have hsecond : T ^ 2 * G * U ≤ 4 * G ^ 33 * U := by
        calc
          _ ≤ (2 * G ^ 16) ^ 2 * G * U := by gcongr
          _ = 4 * G ^ 33 * U := by ring
      change (T * (2 * G * centralTypeBound y) +
        T ^ 2 * (G * centralTypeBound y)) / (y : ℝ) ≤ _
      rw [add_div]
      have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast (show y ≠ 0 by omega)
      rw [show T * (2 * G * centralTypeBound y) / (y : ℝ) =
          T * (2 * G) * U by dsimp only [U]; field_simp,
        show T ^ 2 * (G * centralTypeBound y) / (y : ℝ) =
          T ^ 2 * G * U by dsimp only [U]; field_simp]
      change _ ≤ 8 * (G ^ 33 * U)
      calc
        _ ≤ 4 * G ^ 17 * U + 4 * G ^ 33 * U := add_le_add hfirst hsecond
        _ ≤ 4 * G ^ 33 * U + 4 * G ^ 33 * U := by
          have hp : G ^ 17 ≤ G ^ 33 :=
            pow_le_pow_right₀ hG (by omega : 17 ≤ 33)
          have hmul : 4 * G ^ 17 * U ≤ 4 * G ^ 33 * U := by
            calc
              4 * G ^ 17 * U = 4 * (G ^ 17 * U) := by ring
              _ ≤ 4 * (G ^ 33 * U) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hp hU) (by norm_num)
              _ = 4 * G ^ 33 * U := by ring
          exact add_le_add
            hmul le_rfl
        _ = _ := by ring
    unfold centralChebyshevMajorant
    norm_num only [Nat.cast_pow]
    change (T * (2 * G * centralTypeBound y) +
        T ^ 2 * (G * centralTypeBound y) +
        ((dyadicExponentRange y).card : ℝ) ^ 2 *
          Real.sqrt (centralFourthUniformMajorant y
            (reciprocalVaughanCutoff y) (centralUniformDelta y))) /
        (y : ℝ) ≤ _
    rw [add_div]
    exact add_le_add hsmall (central_fourth_term_div_le hy)
  have hupper : Tendsto (fun y : ℕ ↦ 8 * A y + B y) atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using hA.const_mul 8 |>.add hB
  exact squeeze_zero' (Eventually.of_forall hnonneg) hbound hupper

theorem eventually_centralChebyshev_bound :
    ∀ᶠ y : ℕ in atTop, ∀ {x : ℕ} {X : ℝ},
      x < y → y ≤ 2 * x → 0 < X →
      (y : ℝ) ^ 2 ≤ 4 * X → X ≤ (y : ℝ) ^ 16 →
      ‖weightedChebyshevInterval (reciprocalWeight X) x y‖ ≤
        centralChebyshevMajorant y (reciprocalVaughanCutoff y)
          (centralTypeBound y) (centralUniformDelta y) := by
  have hsizeEvent := eventually_centralCorrelationSizeCondition
  rcases hsizeEvent.exists_forall_of_atTop with ⟨M₀, hM₀⟩
  have hZlarge : ∀ᶠ y : ℕ in atTop, M₀ ≤ inverseSquareUniformScale y :=
    tendsto_inverseSquareUniformScale_atTop.eventually (eventually_ge_atTop M₀)
  filter_upwards [eventually_ge_atTop 4, eventually_inverseSquare_basic_parameters,
    hZlarge] with y hy hbasic hZlargeY
  intro x X hxy hyx hX hXlo hXhi
  let T := reciprocalVaughanCutoff y
  let Z := inverseSquareUniformScale y
  let delta := centralUniformDelta y
  let B := centralTypeBound y
  have hT : 0 < T := reciprocalVaughanCutoff_pos y
  have hZ : 1 ≤ Z := by dsimp only [Z, inverseSquareUniformScale]; omega
  have hdelta : 0 ≤ delta := by
    simpa only [delta] using centralUniformDelta_nonneg y
  have hB : 0 ≤ B := by simpa only [B] using centralTypeBound_nonneg y
  have hTy : T ≤ y := by
    have hTone : T ≤ T ^ 4 := by
      have : 1 ≤ T := hT
      nlinarith [show 1 ≤ T ^ 2 by exact one_le_pow₀ this]
    exact hTone.trans ((show T ^ 4 ≤ 2 * T ^ 4 by omega).trans hbasic.1)
  have hTx : T ^ 4 ≤ x := by
    have htwo : 2 * T ^ 4 ≤ 2 * x := hbasic.1.trans hyx
    omega
  have hsmallM : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      Z ≤ x / q + 1 ∧ x / q + 1 ≤ y := by
    intro q hq hqT
    have hcore : T ^ 2 * Z ≤ x := by
      have htwo : 2 * (T ^ 2 * Z) ≤ 2 * x := by
        simpa [mul_assoc] using hbasic.2.1.trans hyx
      omega
    have hqZ : q * Z ≤ x := (Nat.mul_le_mul_right Z hqT).trans hcore
    have hZdiv : Z ≤ x / q := (Nat.le_div_iff_mul_le (by omega)).2 (by
      simpa [Nat.mul_comm] using hqZ)
    exact ⟨hZdiv.trans (Nat.le_add_right _ _), by
      have := Nat.div_le_self x q
      omega⟩
  have hsmallSize : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      centralCorrelationSizeCondition (x / q + 1) := by
    intro q hq hqT
    exact hM₀ _ (hZlargeY.trans (hsmallM q hq hqT).1)
  have hsmallB : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      1 + adaptiveCorrelationEnvelope (x / q + 1) ≤ B := by
    intro q hq hqT
    have hM := hsmallM q hq hqT
    have henv := adaptiveCorrelationEnvelope_le_uniform hM.1 hM.2
    dsimp only [B, centralTypeBound, delta]
    exact add_le_add le_rfl (henv.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast hM.2) (centralUniformDelta_nonneg y)))
  have hlargeM : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y → Z ≤ L ∧ L ≤ y := by
    intro L hxL hLy
    have hfour : 4 * Z ^ 2 ≤ x := by
      have htwo : 8 * Z ^ 2 ≤ 2 * x := hbasic.2.2.trans hyx
      omega
    have hsq : Z ^ 2 < L ^ 2 := by nlinarith
    have hZL : Z ≤ L := by nlinarith
    exact ⟨hZL, hLy⟩
  have hlargeSize : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      centralCorrelationSizeCondition L := by
    intro L hxL hLy
    exact hM₀ _ (hZlargeY.trans (hlargeM L hxL hLy).1)
  have hlargeEnvelope : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      adaptiveCorrelationEnvelope L ≤ delta * L := by
    intro L hxL hLy
    have hM := hlargeM L hxL hLy
    simpa only [delta] using adaptiveCorrelationEnvelope_le_uniform hM.1 hM.2
  apply norm_weightedChebyshevInterval_central_le hX hT hTy hTx hxy hXlo
    hXhi hyx hB hdelta hsmallSize hsmallB hlargeSize hlargeEnvelope

end

end CentralChebyshevApplication
end Erdos378
