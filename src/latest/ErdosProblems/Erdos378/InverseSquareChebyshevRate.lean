/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.InverseSquareChebyshevAsymptotic

/-!
# Quantitative decay for the inverse-square Chebyshev estimate

The thirty-two-step correlation estimate takes a small positive real power
of its moment.  This file records an intentionally coarse power-rate bound;
it is enough to absorb every logarithm introduced by Vaughan's identity.
-/

open Filter
open scoped Topology

namespace Erdos378
namespace InverseSquareChebyshevRate

open AdaptiveShifts
open CentralAsymptotic
open ReciprocalChebyshevAsymptotic
open InverseSquareChebyshevAsymptotic
open InverseSquareAdaptiveShifts

noncomputable section

theorem eventually_logarithmicSafety_pow_le_rpow (A : ℕ) {s : ℝ}
    (hs : 0 < s) :
    ∀ᶠ y : ℕ in atTop,
      logarithmicSafety y ^ A ≤ (y : ℝ) ^ s := by
  let n : ℕ := 100 * A
  have hs2 : 0 < s / 2 := by linarith
  have hlogpow := eventually_log_natCast_rpow_le_rpow
    (n : ℝ) (s / 2) (by positivity) hs2
  have hgrowth : Tendsto (fun y : ℕ ↦ (y : ℝ) ^ (s / 2)) atTop atTop :=
    (tendsto_rpow_atTop hs2).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hconst : ∀ᶠ y : ℕ in atTop,
      (2 : ℝ) ^ n ≤ (y : ℝ) ^ (s / 2) :=
    hgrowth (eventually_ge_atTop ((2 : ℝ) ^ n))
  have hlogLarge : ∀ᶠ y : ℕ in atTop, 2 ≤ Real.log (y : ℝ) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))) (eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop 1, hlogpow, hconst, hlogLarge] with
      y hy hylog hconstY hlogY
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hlog0 : 0 ≤ Real.log (y : ℝ) := by linarith
  have hadd : Real.log (y : ℝ) + 2 ≤ 2 * Real.log (y : ℝ) := by linarith
  have hlogNat : Real.log (y : ℝ) ^ n ≤ (y : ℝ) ^ (s / 2) := by
    calc
      Real.log (y : ℝ) ^ n =
          Real.log (y : ℝ) ^ (n : ℝ) :=
        (Real.rpow_natCast (Real.log (y : ℝ)) n).symm
      _ ≤ _ := hylog
  unfold logarithmicSafety
  rw [← pow_mul]
  change (Real.log (y : ℝ) + 2) ^ n ≤ (y : ℝ) ^ s
  calc
    _ ≤ (2 * Real.log (y : ℝ)) ^ n := pow_le_pow_left₀ (by linarith) hadd n
    _ = (2 : ℝ) ^ n * Real.log (y : ℝ) ^ n := by rw [mul_pow]
    _ ≤ (y : ℝ) ^ (s / 2) * (y : ℝ) ^ (s / 2) :=
      mul_le_mul hconstY hlogNat (pow_nonneg hlog0 n)
        (Real.rpow_nonneg (by positivity) _)
    _ = (y : ℝ) ^ s := by
      rw [← Real.rpow_add hyR]
      congr 2
      ring

theorem eventually_rpow_le_uniformBase :
    ∀ᶠ y : ℕ in atTop,
      (y : ℝ) ^ (1 / 512 : ℝ) ≤
        (baseShift (inverseSquareUniformScale y) : ℝ) := by
  have hbLarge : ∀ᶠ y : ℕ in atTop,
      2 ≤ baseShift (inverseSquareUniformScale y) := by
    have hb : ∀ᶠ Z : ℕ in atTop, 2 ≤ baseShift Z :=
      CentralAsymptotic.tendsto_baseShift_atTop.eventually (eventually_ge_atTop 2)
    rcases hb.exists_forall_of_atTop with ⟨Z₀, hZ₀⟩
    have hscale : ∀ᶠ y : ℕ in atTop, Z₀ ≤ inverseSquareUniformScale y :=
      tendsto_inverseSquareUniformScale_atTop.eventually (eventually_ge_atTop Z₀)
    filter_upwards [hscale] with y hy
    exact hZ₀ _ hy
  filter_upwards [eventually_ge_atTop 1, hbLarge] with y hy hbLargeY
  let Z := inverseSquareUniformScale y
  let b := baseShift Z
  have hyZ : y < Z ^ 16 := by
    simpa only [Z, inverseSquareUniformScale] using
      CentralAsymptotic.lt_baseShift_succ_pow_sixteen y
  have hZb : Z < (b + 1) ^ 16 := by
    simpa only [b] using CentralAsymptotic.lt_baseShift_succ_pow_sixteen Z
  have hbTwo : b + 1 ≤ 2 * b := by
    change 2 ≤ b at hbLargeY
    omega
  have hnat : y ≤ (2 * b) ^ 256 := by
    calc
      y ≤ Z ^ 16 := hyZ.le
      _ ≤ ((b + 1) ^ 16) ^ 16 := Nat.pow_le_pow_left hZb.le 16
      _ = (b + 1) ^ 256 := by rw [← pow_mul]
      _ ≤ (2 * b) ^ 256 := Nat.pow_le_pow_left hbTwo 256
  have hreal : (y : ℝ) ≤ (2 * (b : ℝ)) ^ 256 := by exact_mod_cast hnat
  have hrpow := Real.rpow_le_rpow (by positivity) hreal
    (by norm_num : (0 : ℝ) ≤ 1 / 512)
  have hrhs : ((2 * (b : ℝ)) ^ 256) ^ (1 / 512 : ℝ) =
      Real.sqrt (2 * (b : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity)]
    rw [show (((256 : ℕ) : ℝ)) * (1 / 512 : ℝ) = 1 / 2 by norm_num]
    exact (Real.sqrt_eq_rpow _).symm
  have hsqrt : Real.sqrt (2 * (b : ℝ)) ≤ (b : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hbLargeY
      calc
        2 * (b : ℝ) ≤ (b : ℝ) * b :=
          mul_le_mul_of_nonneg_right hbR (by positivity)
        _ = (b : ℝ) ^ 2 := by ring
  change (y : ℝ) ^ (1 / 512 : ℝ) ≤ (b : ℝ)
  exact hrpow.trans (hrhs.le.trans hsqrt)

theorem eventually_safety_ratio_uniformBase_le :
    ∀ᶠ y : ℕ in atTop,
      logarithmicSafety y ^ 362 /
          (baseShift (inverseSquareUniformScale y) : ℝ) ≤
        (y : ℝ) ^ (-1 / 4096 : ℝ) := by
  have hsafety := eventually_logarithmicSafety_pow_le_rpow 362
    (show (0 : ℝ) < 1 / 4096 by norm_num)
  filter_upwards [eventually_ge_atTop 1, eventually_rpow_le_uniformBase,
    hsafety] with y hy hbase hsafe
  let b : ℝ := baseShift (inverseSquareUniformScale y)
  let Y : ℝ := y
  have hY : 1 ≤ Y := by
    change (1 : ℝ) ≤ (y : ℝ)
    exact_mod_cast hy
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have hbpos : 0 < b := by
    have : 0 < baseShift (inverseSquareUniformScale y) :=
      baseShift_pos (by unfold inverseSquareUniformScale; omega)
    change (0 : ℝ) < (baseShift (inverseSquareUniformScale y) : ℝ)
    exact_mod_cast this
  have hPpos : 0 < Y ^ (1 / 512 : ℝ) := Real.rpow_pos_of_pos hYpos _
  have hratio : logarithmicSafety y ^ 362 / b ≤
      Y ^ (1 / 4096 : ℝ) / Y ^ (1 / 512 : ℝ) := by
    calc
      _ ≤ logarithmicSafety y ^ 362 / Y ^ (1 / 512 : ℝ) :=
        div_le_div_of_nonneg_left (pow_nonneg (logarithmicSafety_pos hy).le 362)
          hPpos hbase
      _ ≤ _ := div_le_div_of_nonneg_right hsafe hPpos.le
  change logarithmicSafety y ^ 362 / b ≤ Y ^ (-1 / 4096 : ℝ)
  calc
    _ ≤ Y ^ (1 / 4096 : ℝ) / Y ^ (1 / 512 : ℝ) := hratio
    _ = Y ^ (1 / 4096 - 1 / 512 : ℝ) := by
      rw [Real.rpow_sub hYpos]
    _ ≤ Y ^ (-1 / 4096 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hY (by norm_num)

def uniformMomentRateConstant : ℝ :=
  HigherDerivative.vdcMomentConstant 32 *
    (32 + 1 / 256 + inverseSquareTerminalConstant / 32 +
      12 * (2 : ℝ) ^ 101)

lemma uniformMomentRateConstant_nonneg : 0 ≤ uniformMomentRateConstant := by
  unfold uniformMomentRateConstant
  have hV := HigherDerivative.vdcMomentConstant_pos 32
  have hT := inverseSquareTerminalConstant_pos
  positivity

theorem eventually_inverseSquareUniformMoment_le_rate :
    ∀ᶠ y : ℕ in atTop,
      inverseSquareUniformMoment y (inverseSquareUniformScale y)
          (inverseSquareCorrelationCap y) ≤
        uniformMomentRateConstant * (y : ℝ) ^ (-1 / 4096 : ℝ) := by
  filter_upwards [eventually_ge_atTop 4,
    eventually_safety_ratio_uniformBase_le] with y hy hratio
  let S := logarithmicSafety y
  let Z := inverseSquareUniformScale y
  let b : ℝ := baseShift Z
  let R : ℝ := (y : ℝ) ^ (-1 / 4096 : ℝ)
  have hS : 1 ≤ S := (one_lt_logarithmicSafety (by omega)).le
  have hbpos : 0 < b := by
    change (0 : ℝ) < (baseShift Z : ℝ)
    exact_mod_cast baseShift_pos (by dsimp only [Z, inverseSquareUniformScale]; omega)
  have hZpos : (0 : ℝ) < Z := by
    exact_mod_cast (show 0 < Z by dsimp only [Z, inverseSquareUniformScale]; omega)
  have hbZ : b ≤ (Z : ℝ) := by
    change (baseShift Z : ℝ) ≤ (Z : ℝ)
    exact_mod_cast baseShift_le Z
  have hR : 0 ≤ R := Real.rpow_nonneg (by positivity) _
  have hratio' : S ^ 362 / b ≤ R := by
    simpa only [S, Z, b, R] using hratio
  have hone : 1 / b ≤ R := by
    calc
      1 / b ≤ S ^ 362 / b := by
        exact div_le_div_of_nonneg_right (one_le_pow₀ hS) hbpos.le
      _ ≤ R := hratio'
  have hterminal : inverseSquareTerminalConstant * S ^ 64 / (32 * b) ≤
      (inverseSquareTerminalConstant / 32) * R := by
    have hpow : S ^ 64 ≤ S ^ 362 := pow_le_pow_right₀ hS (by omega)
    have hcoeff : 0 ≤ inverseSquareTerminalConstant / 32 :=
      div_nonneg inverseSquareTerminalConstant_pos.le (by norm_num)
    calc
      _ = (inverseSquareTerminalConstant / 32) * (S ^ 64 / b) := by ring
      _ ≤ (inverseSquareTerminalConstant / 32) * (S ^ 362 / b) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hpow hbpos.le) hcoeff
      _ ≤ (inverseSquareTerminalConstant / 32) * R :=
        mul_le_mul_of_nonneg_left hratio' hcoeff
  have hactive :
      (12 * 2 ^ 35 * (2 * (inverseSquareCorrelationCap y : ℝ)) ^ 33) *
          (S ^ 32 / (Z : ℝ)) ≤
        (12 * (2 : ℝ) ^ 101) * R := by
    have hcap := inverseSquareCorrelationCap_pow_mul_safety_le hy
    change (inverseSquareCorrelationCap y : ℝ) ^ 33 * S ^ 32 ≤
      (2 : ℝ) ^ 33 * S ^ 362 at hcap
    have hfrac : S ^ 362 / (Z : ℝ) ≤ S ^ 362 / b :=
      div_le_div_of_nonneg_left (pow_nonneg (zero_le_one.trans hS) 362) hbpos hbZ
    have hA : 0 ≤ 12 * (2 : ℝ) ^ 68 := by positivity
    have hA' : 0 ≤ 12 * (2 : ℝ) ^ 101 := by positivity
    calc
      _ = (12 * (2 : ℝ) ^ 68) *
          (((inverseSquareCorrelationCap y : ℝ) ^ 33 * S ^ 32) /
            (Z : ℝ)) := by ring
      _ ≤ (12 * (2 : ℝ) ^ 68) *
          (((2 : ℝ) ^ 33 * S ^ 362) / (Z : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hcap hZpos.le) hA
      _ = (12 * (2 : ℝ) ^ 101) * (S ^ 362 / (Z : ℝ)) := by ring
      _ ≤ (12 * (2 : ℝ) ^ 101) * (S ^ 362 / b) :=
        mul_le_mul_of_nonneg_left hfrac hA'
      _ ≤ (12 * (2 : ℝ) ^ 101) * R :=
        mul_le_mul_of_nonneg_left hratio' hA'
  have hinner :
      32 / b + 1 / (256 * b) +
          inverseSquareTerminalConstant * S ^ 64 / (32 * b) +
          (12 * 2 ^ 35 * (2 * (inverseSquareCorrelationCap y : ℝ)) ^ 33) *
            (S ^ 32 / (Z : ℝ)) ≤
        (32 + 1 / 256 + inverseSquareTerminalConstant / 32 +
          12 * (2 : ℝ) ^ 101) * R := by
    calc
      _ ≤ 32 * R + (1 / 256) * R +
        (inverseSquareTerminalConstant / 32) * R +
          (12 * (2 : ℝ) ^ 101) * R := by
        have hfirst := mul_le_mul_of_nonneg_left hone (by norm_num : (0 : ℝ) ≤ 32)
        have hsecond := mul_le_mul_of_nonneg_left hone
          (by norm_num : (0 : ℝ) ≤ 1 / 256)
        rw [show 32 / b = 32 * (1 / b) by ring,
          show 1 / (256 * b) = (1 / 256 : ℝ) * (1 / b) by ring]
        linarith
      _ = (32 + 1 / 256 + inverseSquareTerminalConstant / 32 +
          12 * (2 : ℝ) ^ 101) * R := by ring
  calc
    inverseSquareUniformMoment y Z (inverseSquareCorrelationCap y) =
        HigherDerivative.vdcMomentConstant 32 *
          (32 / b + 1 / (256 * b) +
            inverseSquareTerminalConstant * S ^ 64 / (32 * b) +
            (12 * 2 ^ 35 * (2 * (inverseSquareCorrelationCap y : ℝ)) ^ 33) *
              (S ^ 32 / (Z : ℝ))) := rfl
    _ ≤ HigherDerivative.vdcMomentConstant 32 *
        ((32 + 1 / 256 + inverseSquareTerminalConstant / 32 +
          12 * (2 : ℝ) ^ 101) * R) :=
      mul_le_mul_of_nonneg_left hinner
        (HigherDerivative.vdcMomentConstant_pos 32).le
    _ = uniformMomentRateConstant * R := by
      unfold uniformMomentRateConstant
      ring

theorem eventually_inverseSquareUniformMoment_le_pure_rate :
    ∀ᶠ y : ℕ in atTop,
      inverseSquareUniformMoment y (inverseSquareUniformScale y)
          (inverseSquareCorrelationCap y) ≤
        (y : ℝ) ^ (-1 / 8192 : ℝ) := by
  have hgrowth : Tendsto (fun y : ℕ ↦ (y : ℝ) ^ (1 / 8192 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8192)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hconstant : ∀ᶠ y : ℕ in atTop,
      uniformMomentRateConstant ≤ (y : ℝ) ^ (1 / 8192 : ℝ) :=
    hgrowth (eventually_ge_atTop uniformMomentRateConstant)
  filter_upwards [eventually_ge_atTop 1,
    eventually_inverseSquareUniformMoment_le_rate, hconstant] with
      y hy hmoment hconstantY
  have hyR : (0 : ℝ) < y := by positivity
  calc
    inverseSquareUniformMoment y (inverseSquareUniformScale y)
        (inverseSquareCorrelationCap y) ≤
      uniformMomentRateConstant * (y : ℝ) ^ (-1 / 4096 : ℝ) := hmoment
    _ ≤ (y : ℝ) ^ (1 / 8192 : ℝ) *
        (y : ℝ) ^ (-1 / 4096 : ℝ) :=
      mul_le_mul_of_nonneg_right hconstantY (Real.rpow_nonneg (by positivity) _)
    _ = (y : ℝ) ^ (-1 / 8192 : ℝ) := by
      rw [← Real.rpow_add hyR]
      congr 2
      ring

def inverseSquarePowerRate : ℝ :=
  1 / (8192 * (2 ^ 32 : ℕ) : ℝ)

lemma inverseSquarePowerRate_pos : 0 < inverseSquarePowerRate := by
  unfold inverseSquarePowerRate
  positivity

theorem eventually_inverseSquareUniformMoment_rpow_le_rate :
    ∀ᶠ y : ℕ in atTop,
      (inverseSquareUniformMoment y (inverseSquareUniformScale y)
        (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹ ≤
          (y : ℝ) ^ (-inverseSquarePowerRate) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_inverseSquareUniformMoment_le_pure_rate] with y hy hmoment
  have hnonneg : 0 ≤ inverseSquareUniformMoment y (inverseSquareUniformScale y)
      (inverseSquareCorrelationCap y) :=
    inverseSquareUniformMoment_nonneg (by
      unfold inverseSquareUniformScale
      omega)
  have hr := Real.rpow_le_rpow hnonneg hmoment
    (by positivity : (0 : ℝ) ≤ ((2 ^ 32 : ℕ) : ℝ)⁻¹)
  calc
    _ ≤ ((y : ℝ) ^ (-1 / 8192 : ℝ)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹ := hr
    _ = (y : ℝ) ^ (-inverseSquarePowerRate) := by
      rw [← Real.rpow_mul (by positivity)]
      unfold inverseSquarePowerRate
      congr 2
      norm_num

private theorem tendsto_log_pow_mul_cap_inverse_zero :
    Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 100 *
        (34 / (inverseSquareCorrelationCap y : ℝ))) atTop (nhds 0) := by
  have hlogTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpowTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 900)
      atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : 900 ≠ 0)).comp hlogTop
  have hupper : Tendsto (fun y : ℕ ↦ 34 / Real.log (y : ℝ) ^ 900)
      atTop (nhds 0) := by
    have hinv := hpowTop.inv_tendsto_atTop
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply, Pi.inv_apply] using
      hinv.const_mul 34
  have hnonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ Real.log (y : ℝ) ^ 100 *
        (34 / (inverseSquareCorrelationCap y : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 100)
      (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hbound : ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ^ 100 *
          (34 / (inverseSquareCorrelationCap y : ℝ)) ≤
        34 / Real.log (y : ℝ) ^ 900 := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    let G := Real.log (y : ℝ)
    let C : ℝ := inverseSquareCorrelationCap y
    have hG : 1 ≤ G := by
      simpa only [G] using BoundedGaps.Maynard.one_le_log_natCast hy
    have hC : 0 < C := by
      change (0 : ℝ) < (inverseSquareCorrelationCap y : ℝ)
      exact_mod_cast inverseSquareCorrelationCap_pos y
    have hGpos : 0 < G := lt_of_lt_of_le (by norm_num) hG
    have hcap : G ^ 1000 < C := by
      simpa only [G, C] using (inverseSquareCorrelationCap_real_bounds hy).1
    have hdiv : G ^ 100 / C ≤ G ^ 100 / G ^ 1000 :=
      div_le_div_of_nonneg_left (pow_nonneg (zero_le_one.trans hG) 100)
        (pow_pos (lt_of_lt_of_le (by norm_num) hG) 1000) hcap.le
    change G ^ 100 * (34 / C) ≤ 34 / G ^ 900
    calc
      _ = 34 * (G ^ 100 / C) := by ring
      _ ≤ 34 * (G ^ 100 / G ^ 1000) := by gcongr
      _ = 34 / G ^ 900 := by
        field_simp [hGpos.ne']
  exact squeeze_zero' hnonneg hbound hupper

private theorem tendsto_log_pow_mul_scale_inverse_zero :
    Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 100 *
        (34 / (inverseSquareUniformScale y : ℝ))) atTop (nhds 0) := by
  have hrate : Tendsto (fun y : ℕ ↦
      34 * (y : ℝ) ^ (-1 / 4096 : ℝ)) atTop (nhds 0) := by
    have h := ((tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 1 / 4096)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 34
    convert h using 1
    · funext y
      simp only [Function.comp_apply]
      congr 1
      ring_nf
    · norm_num
  have hnonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ Real.log (y : ℝ) ^ 100 *
        (34 / (inverseSquareUniformScale y : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 100)
      (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hbound : ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ^ 100 *
          (34 / (inverseSquareUniformScale y : ℝ)) ≤
        34 * (y : ℝ) ^ (-1 / 4096 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1,
      eventually_safety_ratio_uniformBase_le] with y hy hratio
    have hlogSafety : Real.log (y : ℝ) ^ 100 ≤ logarithmicSafety y := by
      unfold logarithmicSafety
      exact pow_le_pow_left₀ (Real.log_natCast_nonneg y) (by linarith) 100
    have hS : 1 ≤ logarithmicSafety y :=
      (one_lt_logarithmicSafety hy).le
    have hSpow : logarithmicSafety y ≤ logarithmicSafety y ^ 362 := by
      simpa using pow_le_pow_right₀ hS (show (1 : ℕ) ≤ 362 by omega)
    have hbpos : (0 : ℝ) < baseShift (inverseSquareUniformScale y) := by
      exact_mod_cast baseShift_pos (by unfold inverseSquareUniformScale; omega)
    have hbZ : (baseShift (inverseSquareUniformScale y) : ℝ) ≤
        inverseSquareUniformScale y := by
      exact_mod_cast baseShift_le (inverseSquareUniformScale y)
    have hfrac : Real.log (y : ℝ) ^ 100 /
          (inverseSquareUniformScale y : ℝ) ≤
        logarithmicSafety y ^ 362 /
          (baseShift (inverseSquareUniformScale y) : ℝ) := by
      calc
        _ ≤ logarithmicSafety y /
            (inverseSquareUniformScale y : ℝ) :=
          div_le_div_of_nonneg_right hlogSafety (Nat.cast_nonneg _)
        _ ≤ logarithmicSafety y ^ 362 /
            (inverseSquareUniformScale y : ℝ) := by
          exact div_le_div_of_nonneg_right hSpow (Nat.cast_nonneg _)
        _ ≤ logarithmicSafety y ^ 362 /
            (baseShift (inverseSquareUniformScale y) : ℝ) :=
          div_le_div_of_nonneg_left (pow_nonneg (zero_le_one.trans hS) 362)
            hbpos hbZ
    calc
      _ = 34 * (Real.log (y : ℝ) ^ 100 /
          (inverseSquareUniformScale y : ℝ)) := by ring
      _ ≤ 34 * (logarithmicSafety y ^ 362 /
          (baseShift (inverseSquareUniformScale y) : ℝ)) :=
        mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ ≤ 34 * (y : ℝ) ^ (-1 / 4096 : ℝ) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
  exact squeeze_zero' hnonneg hbound hrate

private theorem tendsto_log_pow_mul_moment_rpow_zero :
    Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 100 *
        (8 * (inverseSquareUniformMoment y (inverseSquareUniformScale y)
          (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹))
      atTop (nhds 0) := by
  have hratePos : 0 < inverseSquarePowerRate / 2 := by
    have := inverseSquarePowerRate_pos
    linarith
  have hupper : Tendsto (fun y : ℕ ↦
      8 * (y : ℝ) ^ (-(inverseSquarePowerRate / 2))) atTop (nhds 0) := by
    have h := ((tendsto_rpow_neg_atTop hratePos).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 8
    convert h using 1
    · funext y
      simp only [Function.comp_apply]
    · norm_num
  have hsafety := eventually_logarithmicSafety_pow_le_rpow 1 hratePos
  have hnonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ Real.log (y : ℝ) ^ 100 *
        (8 * (inverseSquareUniformMoment y (inverseSquareUniformScale y)
          (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    have hmoment : 0 ≤ inverseSquareUniformMoment y (inverseSquareUniformScale y)
        (inverseSquareCorrelationCap y) :=
      inverseSquareUniformMoment_nonneg (by unfold inverseSquareUniformScale; omega)
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 100)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hmoment _))
  have hbound : ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ^ 100 *
          (8 * (inverseSquareUniformMoment y (inverseSquareUniformScale y)
            (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹) ≤
        8 * (y : ℝ) ^ (-(inverseSquarePowerRate / 2)) := by
    filter_upwards [eventually_ge_atTop 1, hsafety,
      eventually_inverseSquareUniformMoment_rpow_le_rate] with y hy hs hm
    have hyR : (0 : ℝ) < y := by positivity
    have hlogSafety : Real.log (y : ℝ) ^ 100 ≤ logarithmicSafety y := by
      unfold logarithmicSafety
      exact pow_le_pow_left₀ (Real.log_natCast_nonneg y) (by linarith) 100
    have hs' : logarithmicSafety y ≤
        (y : ℝ) ^ (inverseSquarePowerRate / 2) := by simpa using hs
    have hm0 : 0 ≤
        (inverseSquareUniformMoment y (inverseSquareUniformScale y)
          (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹ :=
      Real.rpow_nonneg (inverseSquareUniformMoment_nonneg (by
        unfold inverseSquareUniformScale
        omega)) _
    calc
      _ = 8 * (Real.log (y : ℝ) ^ 100 *
          (inverseSquareUniformMoment y (inverseSquareUniformScale y)
            (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹) := by ring
      _ ≤ 8 * (logarithmicSafety y *
          (inverseSquareUniformMoment y (inverseSquareUniformScale y)
            (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hlogSafety hm0) (by norm_num)
      _ ≤ 8 * ((y : ℝ) ^ (inverseSquarePowerRate / 2) *
          (y : ℝ) ^ (-inverseSquarePowerRate)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul hs' hm hm0 (Real.rpow_nonneg (by positivity) _)
      _ = 8 * (y : ℝ) ^ (-(inverseSquarePowerRate / 2)) := by
        rw [← Real.rpow_add hyR]
        congr 2
        ring
  exact squeeze_zero' hnonneg hbound hupper

theorem tendsto_log_pow_mul_inverseSquareUniformDelta_zero :
    Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 100 *
        inverseSquareUniformDelta y (inverseSquareUniformScale y)
          (inverseSquareCorrelationCap y)) atTop (nhds 0) := by
  have hsum := tendsto_log_pow_mul_cap_inverse_zero.add
    tendsto_log_pow_mul_scale_inverse_zero |>.add
      tendsto_log_pow_mul_moment_rpow_zero
  unfold inverseSquareUniformDelta
  convert hsum using 1
  · funext y
    ring
  · norm_num

end

end InverseSquareChebyshevRate
end Erdos378
