/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.InverseSquareChebyshevRate

/-!
# The vanishing inverse-square Chebyshev majorant
-/

open Filter
open scoped Topology

namespace Erdos378
namespace InverseSquareChebyshevLimit

open AdaptiveShifts
open ReciprocalChebyshevAsymptotic
open InverseSquareChebyshev
open InverseSquareChebyshevAsymptotic
open InverseSquareChebyshevRate
open InverseSquareVaughanHybrid
open BoundedGaps.Maynard

noncomputable section

def inverseSquareAsymptoticDelta (y : ℕ) : ℝ :=
  inverseSquareUniformDelta y (inverseSquareUniformScale y)
    (inverseSquareCorrelationCap y)

def inverseSquareTypeBound (y : ℕ) : ℝ :=
  3 + 12 * (y : ℝ) / (inverseSquareCorrelationCap y : ℝ) ^ 2 +
    inverseSquareAsymptoticDelta y * y

lemma inverseSquareAsymptoticDelta_nonneg (y : ℕ) :
    0 ≤ inverseSquareAsymptoticDelta y := by
  unfold inverseSquareAsymptoticDelta
  exact inverseSquareUniformDelta_nonneg
    (by unfold inverseSquareUniformScale; omega)
    (inverseSquareCorrelationCap_pos y)

lemma inverseSquareTypeBound_nonneg (y : ℕ) :
    0 ≤ inverseSquareTypeBound y := by
  unfold inverseSquareTypeBound
  apply add_nonneg
  · apply add_nonneg
    · norm_num
    · exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _)
  · exact mul_nonneg (inverseSquareAsymptoticDelta_nonneg y) (Nat.cast_nonneg _)

private theorem tendsto_log_pow_cap_sq_inverse_zero :
    Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 33 *
        (12 / (inverseSquareCorrelationCap y : ℝ) ^ 2))
      atTop (nhds 0) := by
  have hlogTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpowTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 1967)
      atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : 1967 ≠ 0)).comp hlogTop
  have hupper : Tendsto (fun y : ℕ ↦ 12 / Real.log (y : ℝ) ^ 1967)
      atTop (nhds 0) := by
    have hinv := hpowTop.inv_tendsto_atTop
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply, Function.comp_apply] using
      hinv.const_mul 12
  have hnonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ Real.log (y : ℝ) ^ 33 *
        (12 / (inverseSquareCorrelationCap y : ℝ) ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 33)
      (div_nonneg (by norm_num) (sq_nonneg _))
  have hbound : ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ^ 33 *
          (12 / (inverseSquareCorrelationCap y : ℝ) ^ 2) ≤
        12 / Real.log (y : ℝ) ^ 1967 := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    let G := Real.log (y : ℝ)
    let C : ℝ := inverseSquareCorrelationCap y
    have hG : 1 ≤ G := by
      simpa only [G] using BoundedGaps.Maynard.one_le_log_natCast hy
    have hGpos : 0 < G := lt_of_lt_of_le (by norm_num) hG
    have hC : 0 < C := by
      change (0 : ℝ) < (inverseSquareCorrelationCap y : ℝ)
      exact_mod_cast inverseSquareCorrelationCap_pos y
    have hcap : G ^ 1000 < C := by
      simpa only [G, C] using (inverseSquareCorrelationCap_real_bounds hy).1
    have hcapSq : G ^ 2000 ≤ C ^ 2 := by
      calc
        G ^ 2000 = (G ^ 1000) ^ 2 := by rw [← pow_mul]
        _ ≤ C ^ 2 := pow_le_pow_left₀ (pow_nonneg (zero_le_one.trans hG) 1000)
          hcap.le 2
    have hdiv : G ^ 33 / C ^ 2 ≤ G ^ 33 / G ^ 2000 :=
      div_le_div_of_nonneg_left (pow_nonneg (zero_le_one.trans hG) 33)
        (pow_pos hGpos 2000) hcapSq
    change G ^ 33 * (12 / C ^ 2) ≤ 12 / G ^ 1967
    calc
      _ = 12 * (G ^ 33 / C ^ 2) := by ring
      _ ≤ 12 * (G ^ 33 / G ^ 2000) := by gcongr
      _ = 12 / G ^ 1967 := by field_simp [hGpos.ne']
  exact squeeze_zero' hnonneg hbound hupper

private theorem tendsto_log_pow_mul_delta_zero :
    Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 33 * inverseSquareAsymptoticDelta y)
      atTop (nhds 0) := by
  have hupper : Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 100 * inverseSquareAsymptoticDelta y)
      atTop (nhds 0) := by
    simpa only [inverseSquareAsymptoticDelta] using
      tendsto_log_pow_mul_inverseSquareUniformDelta_zero
  have hnonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ Real.log (y : ℝ) ^ 33 * inverseSquareAsymptoticDelta y := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 33)
      (inverseSquareAsymptoticDelta_nonneg y)
  have hbound : ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ^ 33 * inverseSquareAsymptoticDelta y ≤
        Real.log (y : ℝ) ^ 100 * inverseSquareAsymptoticDelta y := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    have hG := BoundedGaps.Maynard.one_le_log_natCast hy
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hG (by omega))
      (inverseSquareAsymptoticDelta_nonneg y)
  exact squeeze_zero' hnonneg hbound hupper

theorem tendsto_log_pow_mul_typeBound_div_zero :
    Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 33 * (inverseSquareTypeBound y / (y : ℝ)))
      atTop (nhds 0) := by
  have hfirst : Tendsto (fun y : ℕ ↦
      3 * (Real.log (y : ℝ) ^ 33 / (y : ℝ))) atTop (nhds 0) := by
    have h := tendsto_log_natCast_rpow_div_rpow (33 : ℝ) 1 (by norm_num)
    have h' := h.const_mul 3
    simp only [Real.rpow_one, mul_zero] at h'
    convert h' using 1
    funext y
    have hp : Real.log (y : ℝ) ^ (33 : ℝ) =
        Real.log (y : ℝ) ^ (33 : ℕ) := by
      rw [show (33 : ℝ) = ((33 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    rw [hp]
  have hsecond := tendsto_log_pow_cap_sq_inverse_zero
  have hthird := tendsto_log_pow_mul_delta_zero
  unfold inverseSquareTypeBound
  have hsum := hfirst.add hsecond |>.add hthird
  convert hsum using 1
  · funext y
    by_cases hy : y = 0
    · simp [hy]
    field_simp
  · norm_num

def inverseSquareFourthError (y : ℕ) : ℝ :=
  6 / (reciprocalVaughanCutoff y : ℝ) +
    98 / (inverseSquareCorrelationCap y : ℝ) +
      inverseSquareAsymptoticDelta y

lemma inverseSquareFourthError_nonneg (y : ℕ) :
    0 ≤ inverseSquareFourthError y := by
  unfold inverseSquareFourthError
  exact add_nonneg (add_nonneg
    (div_nonneg (by norm_num) (Nat.cast_nonneg _))
    (div_nonneg (by norm_num) (Nat.cast_nonneg _)))
    (inverseSquareAsymptoticDelta_nonneg y)

private theorem tendsto_log_eight_mul_cutoff_inverse_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 8 *
      (6 / (reciprocalVaughanCutoff y : ℝ))) atTop (nhds 0) := by
  have hlogTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpowTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 8)
      atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : 8 ≠ 0)).comp hlogTop
  have hupper : Tendsto (fun y : ℕ ↦ 6 / Real.log (y : ℝ) ^ 8)
      atTop (nhds 0) := by
    have hinv := hpowTop.inv_tendsto_atTop
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply, Function.comp_apply] using
      hinv.const_mul 6
  have hnonneg : ∀ᶠ y : ℕ in atTop, 0 ≤ Real.log (y : ℝ) ^ 8 *
      (6 / (reciprocalVaughanCutoff y : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 8)
      (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hbound : ∀ᶠ y : ℕ in atTop, Real.log (y : ℝ) ^ 8 *
      (6 / (reciprocalVaughanCutoff y : ℝ)) ≤
        6 / Real.log (y : ℝ) ^ 8 := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    let G := Real.log (y : ℝ)
    let T : ℝ := reciprocalVaughanCutoff y
    have hG : 1 ≤ G := by
      simpa only [G] using BoundedGaps.Maynard.one_le_log_natCast hy
    have hGpos : 0 < G := lt_of_lt_of_le (by norm_num) hG
    have hT : G ^ 16 < T := by
      simpa only [G, T] using (reciprocalVaughanCutoff_real_bounds hy).1
    have hdiv : G ^ 8 / T ≤ G ^ 8 / G ^ 16 :=
      div_le_div_of_nonneg_left (pow_nonneg (zero_le_one.trans hG) 8)
        (pow_pos hGpos 16) hT.le
    change G ^ 8 * (6 / T) ≤ 6 / G ^ 8
    calc
      _ = 6 * (G ^ 8 / T) := by ring
      _ ≤ 6 * (G ^ 8 / G ^ 16) := by gcongr
      _ = 6 / G ^ 8 := by field_simp [hGpos.ne']
  exact squeeze_zero' hnonneg hbound hupper

private theorem tendsto_log_eight_mul_cap_inverse_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 8 *
      (98 / (inverseSquareCorrelationCap y : ℝ))) atTop (nhds 0) := by
  have hlogTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpowTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 992)
      atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : 992 ≠ 0)).comp hlogTop
  have hupper : Tendsto (fun y : ℕ ↦ 98 / Real.log (y : ℝ) ^ 992)
      atTop (nhds 0) := by
    have hinv := hpowTop.inv_tendsto_atTop
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply, Function.comp_apply] using
      hinv.const_mul 98
  have hnonneg : ∀ᶠ y : ℕ in atTop, 0 ≤ Real.log (y : ℝ) ^ 8 *
      (98 / (inverseSquareCorrelationCap y : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 8)
      (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hbound : ∀ᶠ y : ℕ in atTop, Real.log (y : ℝ) ^ 8 *
      (98 / (inverseSquareCorrelationCap y : ℝ)) ≤
        98 / Real.log (y : ℝ) ^ 992 := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    let G := Real.log (y : ℝ)
    let C : ℝ := inverseSquareCorrelationCap y
    have hG : 1 ≤ G := by
      simpa only [G] using BoundedGaps.Maynard.one_le_log_natCast hy
    have hGpos : 0 < G := lt_of_lt_of_le (by norm_num) hG
    have hC : G ^ 1000 < C := by
      simpa only [G, C] using (inverseSquareCorrelationCap_real_bounds hy).1
    have hdiv : G ^ 8 / C ≤ G ^ 8 / G ^ 1000 :=
      div_le_div_of_nonneg_left (pow_nonneg (zero_le_one.trans hG) 8)
        (pow_pos hGpos 1000) hC.le
    change G ^ 8 * (98 / C) ≤ 98 / G ^ 992
    calc
      _ = 98 * (G ^ 8 / C) := by ring
      _ ≤ 98 * (G ^ 8 / G ^ 1000) := by gcongr
      _ = 98 / G ^ 992 := by field_simp [hGpos.ne']
  exact squeeze_zero' hnonneg hbound hupper

theorem tendsto_log_eight_mul_fourthError_zero :
    Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 8 * inverseSquareFourthError y)
      atTop (nhds 0) := by
  have hdelta : Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 8 * inverseSquareAsymptoticDelta y)
      atTop (nhds 0) := by
    have hupper : Tendsto (fun y : ℕ ↦
        Real.log (y : ℝ) ^ 100 * inverseSquareAsymptoticDelta y)
        atTop (nhds 0) := by
      simpa only [inverseSquareAsymptoticDelta] using
        tendsto_log_pow_mul_inverseSquareUniformDelta_zero
    have hnonneg : ∀ᶠ y : ℕ in atTop,
        0 ≤ Real.log (y : ℝ) ^ 8 * inverseSquareAsymptoticDelta y := by
      filter_upwards [eventually_ge_atTop 1] with y hy
      exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 8)
        (inverseSquareAsymptoticDelta_nonneg y)
    have hbound : ∀ᶠ y : ℕ in atTop,
        Real.log (y : ℝ) ^ 8 * inverseSquareAsymptoticDelta y ≤
          Real.log (y : ℝ) ^ 100 * inverseSquareAsymptoticDelta y := by
      filter_upwards [eventually_ge_atTop 4] with y hy
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (BoundedGaps.Maynard.one_le_log_natCast hy) (by omega))
        (inverseSquareAsymptoticDelta_nonneg y)
    exact squeeze_zero' hnonneg hbound hupper
  unfold inverseSquareFourthError
  have hsum := tendsto_log_eight_mul_cutoff_inverse_zero.add
    tendsto_log_eight_mul_cap_inverse_zero |>.add hdelta
  convert hsum using 1
  · funext y
    ring
  · norm_num

def inverseSquareFourthLimitConstant : ℝ := 16 * Real.sqrt 5000

lemma inverseSquareFourthLimitConstant_nonneg :
    0 ≤ inverseSquareFourthLimitConstant := by
  unfold inverseSquareFourthLimitConstant
  positivity

lemma inverseSquare_fourth_term_div_le {y : ℕ} (hy : 4 ≤ y) :
    ((dyadicExponentRange y).card : ℝ) ^ 2 *
        Real.sqrt (inverseSquareFourthUniformMajorant y
          (reciprocalVaughanCutoff y) (inverseSquareCorrelationCap y)
          (inverseSquareAsymptoticDelta y)) / (y : ℝ) ≤
      inverseSquareFourthLimitConstant *
        Real.sqrt (Real.log (y : ℝ) ^ 8 * inverseSquareFourthError y) := by
  let Y : ℝ := y
  let G : ℝ := Real.log Y
  let T : ℝ := reciprocalVaughanCutoff y
  let E : ℝ := inverseSquareFourthError y
  let D : ℝ := Real.sqrt 5000
  have hY : 0 < Y := by positivity
  have hG : 1 ≤ G := by
    simpa only [G, Y] using BoundedGaps.Maynard.one_le_log_natCast hy
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hT : 0 < T := by
    change (0 : ℝ) < (reciprocalVaughanCutoff y : ℝ)
    exact_mod_cast reciprocalVaughanCutoff_pos y
  have hE : 0 ≤ E := by
    simpa only [E] using inverseSquareFourthError_nonneg y
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hlogTwo : Real.log (2 * Y) ≤ 2 * G := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hY.ne']
    have hlog2 : Real.log 2 ≤ G :=
      Real.log_le_log (by norm_num) (by
        change (2 : ℝ) ≤ (y : ℝ)
        exact_mod_cast (show 2 ≤ y by omega))
    linarith
  have hlogTwo0 : 0 ≤ Real.log (2 * Y) :=
    Real.log_nonneg (by
      have hyR : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
      change (1 : ℝ) ≤ 2 * (y : ℝ)
      linarith)
  have hlogT : Real.log T + 3 ≤ 20 * G := by
    have hbase := log_reciprocalVaughanCutoff_le hy
    change Real.log T ≤ 17 * G at hbase
    linarith [hG]
  have hlogT0 : 0 ≤ Real.log T + 3 := by
    have : 0 ≤ Real.log T := Real.log_nonneg (by
      change (1 : ℝ) ≤ (reciprocalVaughanCutoff y : ℝ)
      exact_mod_cast reciprocalVaughanCutoff_pos y)
    linarith
  have hA : inverseSquareFourthUniformMajorant y
      (reciprocalVaughanCutoff y) (inverseSquareCorrelationCap y)
        (inverseSquareAsymptoticDelta y) ≤
      5000 * Y ^ 2 * G ^ 4 * E := by
    unfold inverseSquareFourthUniformMajorant
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
  have hsqrtA : Real.sqrt (inverseSquareFourthUniformMajorant y
      (reciprocalVaughanCutoff y) (inverseSquareCorrelationCap y)
        (inverseSquareAsymptoticDelta y)) ≤
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
    have hcard0 : (0 : ℝ) ≤ (dyadicExponentRange y).card := by positivity
    nlinarith
  have hsqrtG : Real.sqrt (G ^ 8) = G ^ 4 := by
    rw [show G ^ 8 = (G ^ 4) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hG0 4)]
  change ((dyadicExponentRange y).card : ℝ) ^ 2 *
      Real.sqrt (inverseSquareFourthUniformMajorant y
        (reciprocalVaughanCutoff y) (inverseSquareCorrelationCap y)
          (inverseSquareAsymptoticDelta y)) / Y ≤
    inverseSquareFourthLimitConstant * Real.sqrt (G ^ 8 * E)
  calc
    _ ≤ (16 * G ^ 2) * (D * Y * G ^ 2 * Real.sqrt E) / Y := by
      gcongr
    _ = 16 * D * (G ^ 4 * Real.sqrt E) := by field_simp
    _ = 16 * D * Real.sqrt (G ^ 8 * E) := by
      rw [Real.sqrt_mul (pow_nonneg hG0 8), hsqrtG]
    _ = inverseSquareFourthLimitConstant * Real.sqrt (G ^ 8 * E) := by
      unfold inverseSquareFourthLimitConstant
      rfl

theorem tendsto_inverseSquare_fourth_term_div_zero :
    Tendsto (fun y : ℕ ↦
      ((dyadicExponentRange y).card : ℝ) ^ 2 *
        Real.sqrt (inverseSquareFourthUniformMajorant y
          (reciprocalVaughanCutoff y) (inverseSquareCorrelationCap y)
          (inverseSquareAsymptoticDelta y)) / (y : ℝ)) atTop (nhds 0) := by
  have hupper : Tendsto (fun y : ℕ ↦ inverseSquareFourthLimitConstant *
      Real.sqrt (Real.log (y : ℝ) ^ 8 * inverseSquareFourthError y))
      atTop (nhds 0) := by
    have hsqrt := tendsto_log_eight_mul_fourthError_zero.sqrt
    norm_num at hsqrt
    simpa only [mul_zero] using hsqrt.const_mul inverseSquareFourthLimitConstant
  have hnonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ ((dyadicExponentRange y).card : ℝ) ^ 2 *
        Real.sqrt (inverseSquareFourthUniformMajorant y
          (reciprocalVaughanCutoff y) (inverseSquareCorrelationCap y)
          (inverseSquareAsymptoticDelta y)) / (y : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    positivity
  have hbound : ∀ᶠ y : ℕ in atTop,
      ((dyadicExponentRange y).card : ℝ) ^ 2 *
        Real.sqrt (inverseSquareFourthUniformMajorant y
          (reciprocalVaughanCutoff y) (inverseSquareCorrelationCap y)
          (inverseSquareAsymptoticDelta y)) / (y : ℝ) ≤
      inverseSquareFourthLimitConstant *
        Real.sqrt (Real.log (y : ℝ) ^ 8 * inverseSquareFourthError y) := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    exact inverseSquare_fourth_term_div_le hy
  exact squeeze_zero' hnonneg hbound hupper

lemma inverseSquare_type_terms_div_le {y : ℕ} (hy : 4 ≤ y) :
    ((reciprocalVaughanCutoff y : ℝ) *
        (2 * Real.log (y : ℝ) * inverseSquareTypeBound y) +
      (((reciprocalVaughanCutoff y) ^ 2 : ℕ) : ℝ) *
        (Real.log (y : ℝ) * inverseSquareTypeBound y)) / (y : ℝ) ≤
      8 * (Real.log (y : ℝ) ^ 33 *
        (inverseSquareTypeBound y / (y : ℝ))) := by
  let G := Real.log (y : ℝ)
  let T : ℝ := reciprocalVaughanCutoff y
  let B := inverseSquareTypeBound y
  have hG : 1 ≤ G := by
    simpa only [G] using BoundedGaps.Maynard.one_le_log_natCast hy
  have hT : T ≤ 2 * G ^ 16 := by
    simpa only [T, G] using reciprocalVaughanCutoff_le_two_log_pow hy
  have hB : 0 ≤ B := by simpa only [B] using inverseSquareTypeBound_nonneg y
  have hT0 : 0 ≤ T := by positivity
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hY : (0 : ℝ) < y := by positivity
  have hfirst : T * (2 * G * B) ≤ 4 * G ^ 33 * B := by
    calc
      _ ≤ (2 * G ^ 16) * (2 * G * B) := by gcongr
      _ = 4 * G ^ 17 * B := by ring
      _ ≤ 4 * G ^ 33 * B := by
        gcongr
        omega
  have hsecond : T ^ 2 * (G * B) ≤ 4 * G ^ 33 * B := by
    calc
      _ ≤ (2 * G ^ 16) ^ 2 * (G * B) := by gcongr
      _ = 4 * G ^ 33 * B := by ring
  push_cast
  change (T * (2 * G * B) + T ^ 2 * (G * B)) / (y : ℝ) ≤
    8 * (G ^ 33 * (B / (y : ℝ)))
  rw [div_le_iff₀ hY]
  calc
    _ ≤ 4 * G ^ 33 * B + 4 * G ^ 33 * B := add_le_add hfirst hsecond
    _ = (8 * (G ^ 33 * (B / (y : ℝ)))) * (y : ℝ) := by
      field_simp
      ring

theorem tendsto_inverseSquare_type_terms_div_zero :
    Tendsto (fun y : ℕ ↦
      ((reciprocalVaughanCutoff y : ℝ) *
          (2 * Real.log (y : ℝ) * inverseSquareTypeBound y) +
        (((reciprocalVaughanCutoff y) ^ 2 : ℕ) : ℝ) *
          (Real.log (y : ℝ) * inverseSquareTypeBound y)) / (y : ℝ))
      atTop (nhds 0) := by
  have hupper : Tendsto (fun y : ℕ ↦
      8 * (Real.log (y : ℝ) ^ 33 *
        (inverseSquareTypeBound y / (y : ℝ)))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      tendsto_log_pow_mul_typeBound_div_zero.const_mul 8
  have hnonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ ((reciprocalVaughanCutoff y : ℝ) *
          (2 * Real.log (y : ℝ) * inverseSquareTypeBound y) +
        (((reciprocalVaughanCutoff y) ^ 2 : ℕ) : ℝ) *
          (Real.log (y : ℝ) * inverseSquareTypeBound y)) / (y : ℝ) := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    have hG : 0 ≤ Real.log (y : ℝ) :=
      (zero_le_one.trans (BoundedGaps.Maynard.one_le_log_natCast hy))
    have hB := inverseSquareTypeBound_nonneg y
    apply div_nonneg
    · exact add_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) hG) hB))
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hG hB))
    · exact Nat.cast_nonneg _
  have hbound : ∀ᶠ y : ℕ in atTop,
      ((reciprocalVaughanCutoff y : ℝ) *
          (2 * Real.log (y : ℝ) * inverseSquareTypeBound y) +
        (((reciprocalVaughanCutoff y) ^ 2 : ℕ) : ℝ) *
          (Real.log (y : ℝ) * inverseSquareTypeBound y)) / (y : ℝ) ≤
      8 * (Real.log (y : ℝ) ^ 33 *
        (inverseSquareTypeBound y / (y : ℝ))) := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    exact inverseSquare_type_terms_div_le hy
  exact squeeze_zero' hnonneg hbound hupper

theorem tendsto_inverseSquareChebyshevMajorant_div_zero :
    Tendsto (fun y : ℕ ↦
      inverseSquareChebyshevMajorant y (reciprocalVaughanCutoff y)
        (inverseSquareCorrelationCap y) (inverseSquareTypeBound y)
        (inverseSquareAsymptoticDelta y) / (y : ℝ)) atTop (nhds 0) := by
  unfold inverseSquareChebyshevMajorant
  have hsum := tendsto_inverseSquare_type_terms_div_zero.add
    tendsto_inverseSquare_fourth_term_div_zero
  convert hsum using 1
  · funext y
    by_cases hy : y = 0
    · simp [hy]
    field_simp
  · norm_num

end

end InverseSquareChebyshevLimit
end Erdos378
