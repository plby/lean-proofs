/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.HighIndexCutoffs

/-!
# Quantitative Chebyshev bounds for the high-index split
-/

open Filter
open scoped Topology

namespace Erdos378
namespace HighIndexChebyshev

open AdaptiveShifts
open CentralAsymptotic
open CentralChebyshev
open CentralChebyshevApplication
open CentralCorrelation
open CentralVaughanFourth
open InverseSquareChebyshev
open InverseSquareChebyshevAsymptotic
open InverseSquareChebyshevApplication
open InverseSquareChebyshevLimit
open InverseSquareChebyshevRate
open InverseSquareCorrelation
open InverseSquareAdaptiveShifts
open InverseSquareCentralCorrelation
open InverseSquareHybridAsymptotic
open InverseSquareProductInterval
open InverseSquareVaughanHybrid
open PrimeWeightedInterval
open PrimeReciprocal
open ReciprocalChebyshevAsymptotic
open HighIndexCutoffs
open BoundedGaps.Maynard

noncomputable section

/-- The uniform central correlation error beats the ninety-eighth power of
the outer logarithm.  The exponent `98` is the last convenient integral
power below the `100` built into `logarithmicSafety`. -/
theorem tendsto_log_98_mul_centralUniformDelta_zero :
    Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 98 * centralUniformDelta y) atTop (nhds 0) := by
  let Z : ℕ → ℕ := inverseSquareUniformScale
  have hZTop : Tendsto Z atTop atTop := tendsto_inverseSquareUniformScale_atTop
  have hlogZTop : Tendsto (fun y : ℕ ↦ Real.log (Z y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hZTop)
  have hfirstUpper : Tendsto (fun y : ℕ ↦
      34 * (16 : ℝ) ^ 98 / Real.log (Z y : ℝ) ^ 2) atTop (nhds 0) := by
    have hp : Tendsto (fun y : ℕ ↦ Real.log (Z y : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (α := ℝ) (by norm_num : 2 ≠ 0)).comp hlogZTop
    have hi := hp.inv_tendsto_atTop.const_mul (34 * (16 : ℝ) ^ 98)
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply, Function.comp_apply] using hi
  have hfirstNonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ Real.log (y : ℝ) ^ 98 *
        (34 / logarithmicSafety (Z y)) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 98)
      (div_nonneg (by norm_num) (by unfold logarithmicSafety; positivity))
  have hfirstBound : ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ^ 98 *
          (34 / logarithmicSafety (Z y)) ≤
        34 * (16 : ℝ) ^ 98 / Real.log (Z y : ℝ) ^ 2 := by
    filter_upwards [eventually_ge_atTop 4,
      hZTop.eventually (eventually_ge_atTop 3)] with y hy hZ
    let G : ℝ := Real.log (y : ℝ)
    let H : ℝ := Real.log (Z y : ℝ)
    have hG : 0 ≤ G := by dsimp only [G]; exact Real.log_natCast_nonneg y
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
    have hnum : G ^ 98 ≤ (16 : ℝ) ^ 98 * H ^ 98 := by
      calc
        G ^ 98 ≤ (16 * H) ^ 98 := pow_le_pow_left₀ hG hlog 98
        _ = (16 : ℝ) ^ 98 * H ^ 98 := by rw [mul_pow]
    have hden : H ^ 100 ≤ logarithmicSafety (Z y) := by
      unfold logarithmicSafety
      exact pow_le_pow_left₀ hH.le (by linarith) 100
    change G ^ 98 * (34 / logarithmicSafety (Z y)) ≤
      34 * 16 ^ 98 / H ^ 2
    calc
      _ = 34 * (G ^ 98 / logarithmicSafety (Z y)) := by ring
      _ ≤ 34 * (G ^ 98 / H ^ 100) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact div_le_div_of_nonneg_left (pow_nonneg hG 98)
          (pow_pos hH 100) hden
      _ ≤ 34 * (((16 : ℝ) ^ 98 * H ^ 98) / H ^ 100) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact div_le_div_of_nonneg_right hnum (pow_nonneg hH.le 100)
      _ = 34 * (16 : ℝ) ^ 98 / H ^ 2 := by field_simp [hH.ne']
  have hfirst : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 98 *
      (34 / logarithmicSafety (Z y))) atTop (nhds 0) :=
    squeeze_zero' hfirstNonneg hfirstBound hfirstUpper
  have hrate : Tendsto (fun y : ℕ ↦
      8 * (Real.log (y : ℝ) ^ 98 *
        (y : ℝ) ^ (-inverseSquarePowerRate))) atTop (nhds 0) := by
    have hp : 0 < inverseSquarePowerRate := inverseSquarePowerRate_pos
    have h := tendsto_log_natCast_rpow_div_rpow
      (98 : ℝ) inverseSquarePowerRate hp
    have h' : Tendsto (fun y : ℕ ↦
        8 * (Real.log (y : ℝ) ^ (98 : ℝ) /
          (y : ℝ) ^ inverseSquarePowerRate)) atTop (nhds 0) := by
      simpa using h.const_mul 8
    apply h'.congr'
    filter_upwards [eventually_gt_atTop 1] with y hy
    have hy0 : (0 : ℝ) < y := by positivity
    rw [Real.rpow_neg hy0.le]
    simp only [div_eq_mul_inv]
    congr 2
    exact Real.rpow_natCast _ 98
  have hsecondNonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ Real.log (y : ℝ) ^ 98 *
        (8 * inverseSquareUniformMoment y (inverseSquareUniformScale y)
          (inverseSquareCorrelationCap y) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    have hm0 : 0 ≤ inverseSquareUniformMoment y
        (inverseSquareUniformScale y) (inverseSquareCorrelationCap y) :=
      inverseSquareUniformMoment_nonneg
        (show 1 ≤ inverseSquareUniformScale y by
          unfold inverseSquareUniformScale; omega)
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 98)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hm0 _))
  have hsecondBound : ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ^ 98 *
          (8 * inverseSquareUniformMoment y (inverseSquareUniformScale y)
            (inverseSquareCorrelationCap y) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹) ≤
        8 * (Real.log (y : ℝ) ^ 98 *
          (y : ℝ) ^ (-inverseSquarePowerRate)) := by
    filter_upwards [eventually_inverseSquareUniformMoment_rpow_le_rate,
      eventually_ge_atTop 1] with y hm hy
    have hlog0 : 0 ≤ Real.log (y : ℝ) := Real.log_natCast_nonneg y
    calc
      _ = 8 * (Real.log (y : ℝ) ^ 98 *
          inverseSquareUniformMoment y (inverseSquareUniformScale y)
            (inverseSquareCorrelationCap y) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹) := by ring
      _ ≤ 8 * (Real.log (y : ℝ) ^ 98 *
          (y : ℝ) ^ (-inverseSquarePowerRate)) := by gcongr
  have hsecond : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 98 *
      (8 * inverseSquareUniformMoment y (inverseSquareUniformScale y)
        (inverseSquareCorrelationCap y) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹))
      atTop (nhds 0) := squeeze_zero' hsecondNonneg hsecondBound hrate
  unfold centralUniformDelta
  convert hfirst.add hsecond using 1
  · funext y
    ring
  · norm_num

lemma tendsto_log_pow_mul_centralUniformDelta_zero_of_le
    {a : ℕ} (ha : a ≤ 98) :
    Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ a * centralUniformDelta y) atTop (nhds 0) := by
  have hnonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ Real.log (y : ℝ) ^ a * centralUniformDelta y := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) a)
      (centralUniformDelta_nonneg y)
  have hbound : ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ^ a * centralUniformDelta y ≤
        Real.log (y : ℝ) ^ 98 * centralUniformDelta y := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀
        (BoundedGaps.Maynard.one_le_log_natCast hy) ha)
      (centralUniformDelta_nonneg y)
  exact squeeze_zero' hnonneg hbound
    tendsto_log_98_mul_centralUniformDelta_zero

def nearTypeBound (y : ℕ) : ℝ := 1 + centralUniformDelta y * y

def nearFourthError (y : ℕ) : ℝ :=
  2 / (nearVaughanCutoff y : ℝ) + centralUniformDelta y

def nearChebyshevMajorant (y : ℕ) : ℝ :=
  centralChebyshevMajorant y (nearVaughanCutoff y)
    (nearTypeBound y) (centralUniformDelta y)

def farTypeBound (y : ℕ) : ℝ :=
  3 + 12 * (y : ℝ) / (farSeparation y : ℝ) ^ 2 +
    inverseSquareAsymptoticDelta y * y

def farFourthError (y : ℕ) : ℝ :=
  6 / (farVaughanCutoff y : ℝ) +
    98 / (farSeparation y : ℝ) + inverseSquareAsymptoticDelta y

def farChebyshevMajorant (y : ℕ) : ℝ :=
  inverseSquareChebyshevMajorant y (farVaughanCutoff y)
    (farSeparation y) (farTypeBound y) (inverseSquareAsymptoticDelta y)

lemma nearTypeBound_nonneg (y : ℕ) : 0 ≤ nearTypeBound y := by
  unfold nearTypeBound
  exact add_nonneg (by norm_num)
    (mul_nonneg (centralUniformDelta_nonneg y) (Nat.cast_nonneg _))

lemma nearFourthError_nonneg (y : ℕ) : 0 ≤ nearFourthError y := by
  unfold nearFourthError
  exact add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _))
    (centralUniformDelta_nonneg y)

lemma farTypeBound_nonneg (y : ℕ) : 0 ≤ farTypeBound y := by
  unfold farTypeBound
  exact add_nonneg (add_nonneg (by norm_num)
    (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _)))
    (mul_nonneg (inverseSquareAsymptoticDelta_nonneg y) (Nat.cast_nonneg _))

lemma farFourthError_nonneg (y : ℕ) : 0 ≤ farFourthError y := by
  unfold farFourthError
  exact add_nonneg (add_nonneg
    (div_nonneg (by norm_num) (Nat.cast_nonneg _))
    (div_nonneg (by norm_num) (Nat.cast_nonneg _)))
    (inverseSquareAsymptoticDelta_nonneg y)

theorem tendsto_log_97_mul_nearTypeBound_div_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 97 *
      (nearTypeBound y / (y : ℝ))) atTop (nhds 0) := by
  have hfirst : Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 97 / (y : ℝ)) atTop (nhds 0) := by
    have h := tendsto_log_natCast_rpow_div_rpow (97 : ℝ) 1 (by norm_num)
    have h' : Tendsto (fun y : ℕ ↦
        Real.log (y : ℝ) ^ (97 : ℝ) / (y : ℝ)) atTop (nhds 0) := by
      simpa only [Real.rpow_one] using h
    apply h'.congr'
    filter_upwards with y
    congr 1
    exact Real.rpow_natCast _ 97
  have hsecond :=
    tendsto_log_pow_mul_centralUniformDelta_zero_of_le (a := 97) (by omega)
  unfold nearTypeBound
  convert hfirst.add hsecond using 1
  · funext y
    by_cases hy : y = 0
    · simp [hy]
    field_simp
  · norm_num

theorem tendsto_log_39_mul_nearFourthError_zero :
    Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 39 * nearFourthError y) atTop (nhds 0) := by
  have hcut : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 39 *
      (2 / (nearVaughanCutoff y : ℝ))) atTop (nhds 0) := by
    have hupper : Tendsto (fun y : ℕ ↦ 2 / Real.log (y : ℝ))
        atTop (nhds 0) := by
      have hlogTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply,
        Function.comp_apply] using hlogTop.inv_tendsto_atTop.const_mul 2
    have hnonneg : ∀ᶠ y : ℕ in atTop,
        0 ≤ Real.log (y : ℝ) ^ 39 *
          (2 / (nearVaughanCutoff y : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with y hy
      positivity
    have hbound : ∀ᶠ y : ℕ in atTop,
        Real.log (y : ℝ) ^ 39 *
            (2 / (nearVaughanCutoff y : ℝ)) ≤
          2 / Real.log (y : ℝ) := by
      filter_upwards [eventually_ge_atTop 4] with y hy
      let G := Real.log (y : ℝ)
      let T : ℝ := nearVaughanCutoff y
      have hG : 1 ≤ G := by
        simpa only [G] using BoundedGaps.Maynard.one_le_log_natCast hy
      have hT : G ^ 40 < T := by
        simpa only [G, T, nearVaughanCutoff] using
          (logPowerCutoff_real_bounds (e := 40) (show 1 ≤ y by omega)).1
      change G ^ 39 * (2 / T) ≤ 2 / G
      calc
        _ = 2 * (G ^ 39 / T) := by ring
        _ ≤ 2 * (G ^ 39 / G ^ 40) := by gcongr
        _ = 2 / G := by field_simp [show G ≠ 0 by positivity]
    exact squeeze_zero' hnonneg hbound hupper
  have hdelta :=
    tendsto_log_pow_mul_centralUniformDelta_zero_of_le (a := 39) (by omega)
  unfold nearFourthError
  convert hcut.add hdelta using 1
  · funext y
    ring
  · norm_num

theorem tendsto_log_15_mul_farTypeBound_div_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 15 *
      (farTypeBound y / (y : ℝ))) atTop (nhds 0) := by
  have hfirst : Tendsto (fun y : ℕ ↦
      3 * (Real.log (y : ℝ) ^ 15 / (y : ℝ))) atTop (nhds 0) := by
    have h := tendsto_log_natCast_rpow_div_rpow (15 : ℝ) 1 (by norm_num)
    have h' : Tendsto (fun y : ℕ ↦
        3 * (Real.log (y : ℝ) ^ (15 : ℝ) / (y : ℝ)))
        atTop (nhds 0) := by
      simpa only [Real.rpow_one, mul_zero] using h.const_mul 3
    apply h'.congr'
    filter_upwards with y
    congr 2
    exact Real.rpow_natCast _ 15
  have hsep : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 15 *
      (12 / (farSeparation y : ℝ) ^ 2)) atTop (nhds 0) := by
    have hupper : Tendsto (fun y : ℕ ↦ 12 / Real.log (y : ℝ))
        atTop (nhds 0) := by
      have hlogTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply,
        Function.comp_apply] using hlogTop.inv_tendsto_atTop.const_mul 12
    have hnonneg : ∀ᶠ y : ℕ in atTop,
        0 ≤ Real.log (y : ℝ) ^ 15 *
          (12 / (farSeparation y : ℝ) ^ 2) := by
      filter_upwards [eventually_ge_atTop 1] with y hy
      positivity
    have hbound : ∀ᶠ y : ℕ in atTop,
        Real.log (y : ℝ) ^ 15 *
            (12 / (farSeparation y : ℝ) ^ 2) ≤
          12 / Real.log (y : ℝ) := by
      filter_upwards [eventually_ge_atTop 4] with y hy
      let G := Real.log (y : ℝ)
      let H : ℝ := farSeparation y
      have hG : 1 ≤ G := by
        simpa only [G] using BoundedGaps.Maynard.one_le_log_natCast hy
      have hH : G ^ 8 < H := by
        simpa only [G, H, farSeparation] using
          (logPowerCutoff_real_bounds (e := 8) (show 1 ≤ y by omega)).1
      have hHsq : G ^ 16 ≤ H ^ 2 := by
        calc G ^ 16 = (G ^ 8) ^ 2 := by ring
          _ ≤ H ^ 2 := by gcongr
      change G ^ 15 * (12 / H ^ 2) ≤ 12 / G
      calc
        _ = 12 * (G ^ 15 / H ^ 2) := by ring
        _ ≤ 12 * (G ^ 15 / G ^ 16) := by gcongr
        _ = 12 / G := by field_simp [show G ≠ 0 by positivity]
    exact squeeze_zero' hnonneg hbound hupper
  have hdelta : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 15 *
      inverseSquareAsymptoticDelta y) atTop (nhds 0) := by
    have h : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 100 *
        inverseSquareAsymptoticDelta y) atTop (nhds 0) := by
      simpa only [inverseSquareAsymptoticDelta] using
        tendsto_log_pow_mul_inverseSquareUniformDelta_zero
    have hnonneg : ∀ᶠ y : ℕ in atTop,
        0 ≤ Real.log (y : ℝ) ^ 15 * inverseSquareAsymptoticDelta y := by
      filter_upwards [eventually_ge_atTop 1] with y hy
      exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 15)
        (inverseSquareAsymptoticDelta_nonneg y)
    have hbound : ∀ᶠ y : ℕ in atTop,
        Real.log (y : ℝ) ^ 15 * inverseSquareAsymptoticDelta y ≤
          Real.log (y : ℝ) ^ 100 * inverseSquareAsymptoticDelta y := by
      filter_upwards [eventually_ge_atTop 4] with y hy
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (BoundedGaps.Maynard.one_le_log_natCast hy)
          (by omega)) (inverseSquareAsymptoticDelta_nonneg y)
    exact squeeze_zero' hnonneg hbound h
  unfold farTypeBound
  have hsum := hfirst.add hsep |>.add hdelta
  convert hsum using 1
  · funext y
    by_cases hy : y = 0
    · simp [hy]
    field_simp
  · norm_num

def nearFourthLimitConstant : ℝ := 16 * Real.sqrt 20

lemma nearFourthLimitConstant_nonneg : 0 ≤ nearFourthLimitConstant := by
  unfold nearFourthLimitConstant
  positivity

lemma near_fourth_term_scaled_le {y : ℕ} (hy : 4 ≤ y)
    (hlogT : Real.log (nearVaughanCutoff y : ℝ) + 3 ≤
      Real.sqrt (Real.log (y : ℝ))) :
    Real.log (y : ℝ) ^ 16 *
        (((dyadicExponentRange y).card : ℝ) ^ 2 *
          Real.sqrt (centralFourthUniformMajorant y
            (nearVaughanCutoff y) (centralUniformDelta y)) / (y : ℝ)) ≤
      nearFourthLimitConstant *
        Real.sqrt (Real.log (y : ℝ) ^ 39 * nearFourthError y) := by
  let Y : ℝ := y
  let G : ℝ := Real.log Y
  let T : ℝ := nearVaughanCutoff y
  let E : ℝ := nearFourthError y
  let D : ℝ := Real.sqrt 20
  have hY : 0 < Y := by positivity
  have hG : 1 ≤ G := by
    simpa only [G, Y] using BoundedGaps.Maynard.one_le_log_natCast hy
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hT : 0 < T := by
    change (0 : ℝ) < nearVaughanCutoff y
    exact_mod_cast logPowerCutoff_pos 40 y
  have hE : 0 ≤ E := by simpa only [E] using nearFourthError_nonneg y
  have hlogTwo : Real.log (2 * Y) ≤ 2 * G := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hY.ne']
    have hlog2 : Real.log 2 ≤ G :=
      Real.log_le_log (by norm_num) (by
        change (2 : ℝ) ≤ (y : ℝ)
        exact_mod_cast (show 2 ≤ y by omega))
    linarith
  have hlogTwo0 : 0 ≤ Real.log (2 * Y) :=
    Real.log_nonneg (by
      change (1 : ℝ) ≤ 2 * (y : ℝ)
      exact_mod_cast (show 1 ≤ 2 * y by omega))
  have hlogT0 : 0 ≤ Real.log T + 3 := by
    have hTone : (1 : ℝ) ≤ T := by
      change (1 : ℝ) ≤ (nearVaughanCutoff y : ℝ)
      exact_mod_cast (show 1 ≤ logPowerCutoff 40 y by
        exact logPowerCutoff_pos 40 y)
    linarith [Real.log_nonneg hTone]
  have hsqrtG0 : 0 ≤ Real.sqrt G := Real.sqrt_nonneg _
  have hA : centralFourthUniformMajorant y (nearVaughanCutoff y)
      (centralUniformDelta y) ≤ 20 * Y ^ 2 * G ^ 3 * E := by
    unfold centralFourthUniformMajorant
    change (8 / 3 : ℝ) * Y ^ 2 * Real.log (2 * Y) ^ 2 *
      (Real.log T + 3) ^ 2 * E ≤ _
    calc
      _ ≤ (8 / 3 : ℝ) * Y ^ 2 * (2 * G) ^ 2 *
          (Real.sqrt G) ^ 2 * E := by gcongr
      _ = (32 / 3 : ℝ) * Y ^ 2 * G ^ 3 * E := by
        rw [Real.sq_sqrt hG0]
        ring
      _ ≤ 20 * Y ^ 2 * G ^ 3 * E := by
        have hrest : 0 ≤ Y ^ 2 * G ^ 3 * E := by positivity
        nlinarith
  have hDsq : D ^ 2 = 20 := by
    dsimp only [D]
    rw [Real.sq_sqrt]
    norm_num
  have hsqrtA : Real.sqrt (centralFourthUniformMajorant y
      (nearVaughanCutoff y) (centralUniformDelta y)) ≤
      D * Y * Real.sqrt (G ^ 3 * E) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    calc
      _ ≤ 20 * Y ^ 2 * G ^ 3 * E := hA
      _ = (D * Y * Real.sqrt (G ^ 3 * E)) ^ 2 := by
        rw [mul_pow, mul_pow, hDsq, Real.sq_sqrt (mul_nonneg
          (pow_nonneg hG0 3) hE)]
        ring
  have hcard := card_dyadicExponentRange_le_four_log hy
  change ((dyadicExponentRange y).card : ℝ) ≤ 4 * G at hcard
  have hcardSq : ((dyadicExponentRange y).card : ℝ) ^ 2 ≤ 16 * G ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (dyadicExponentRange y).card by positivity]
  have hsqrt36 : Real.sqrt (G ^ 36) = G ^ 18 := by
    rw [show G ^ 36 = (G ^ 18) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hG0 18)]
  have hsqrtSplit : Real.sqrt (G ^ 39 * E) =
      G ^ 18 * Real.sqrt (G ^ 3 * E) := by
    rw [show G ^ 39 * E = G ^ 36 * (G ^ 3 * E) by ring,
      Real.sqrt_mul (pow_nonneg hG0 36), hsqrt36]
  change G ^ 16 * (((dyadicExponentRange y).card : ℝ) ^ 2 *
      Real.sqrt (centralFourthUniformMajorant y
        (nearVaughanCutoff y) (centralUniformDelta y)) / Y) ≤
    16 * D * Real.sqrt (G ^ 39 * E)
  calc
    _ ≤ G ^ 16 * ((16 * G ^ 2) *
        (D * Y * Real.sqrt (G ^ 3 * E)) / Y) := by gcongr
    _ = 16 * D * (G ^ 18 * Real.sqrt (G ^ 3 * E)) := by
      field_simp
    _ = 16 * D * Real.sqrt (G ^ 39 * E) := by rw [hsqrtSplit]

theorem tendsto_nearChebyshevMajorant_scaled_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 16 *
      (nearChebyshevMajorant y / (y : ℝ))) atTop (nhds 0) := by
  let A : ℕ → ℝ := fun y ↦ Real.log (y : ℝ) ^ 97 *
    (nearTypeBound y / (y : ℝ))
  let B : ℕ → ℝ := fun y ↦ nearFourthLimitConstant *
    Real.sqrt (Real.log (y : ℝ) ^ 39 * nearFourthError y)
  have hA : Tendsto A atTop (nhds 0) :=
    tendsto_log_97_mul_nearTypeBound_div_zero
  have hB : Tendsto B atTop (nhds 0) := by
    have hs := tendsto_log_39_mul_nearFourthError_zero.sqrt
    simpa only [B, Real.sqrt_zero, mul_zero] using
      hs.const_mul nearFourthLimitConstant
  have hlogQuarter := eventually_log_logPowerCutoff_add_three_le 40
  have hnonneg : ∀ y : ℕ, 0 ≤ Real.log (y : ℝ) ^ 16 *
      (nearChebyshevMajorant y / (y : ℝ)) := by
    intro y
    have hmaj : 0 ≤ nearChebyshevMajorant y := by
      unfold nearChebyshevMajorant centralChebyshevMajorant
      exact add_nonneg (add_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
          (mul_nonneg (by norm_num) (Real.log_natCast_nonneg y))
          (nearTypeBound_nonneg y)))
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
          (Real.log_natCast_nonneg y) (nearTypeBound_nonneg y))))
        (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 16)
      (div_nonneg hmaj (Nat.cast_nonneg _))
  have hbound : ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ^ 16 *
          (nearChebyshevMajorant y / (y : ℝ)) ≤
        8 * A y + B y := by
    filter_upwards [eventually_ge_atTop 4, hlogQuarter] with y hy hquarter
    let G : ℝ := Real.log (y : ℝ)
    let T : ℝ := nearVaughanCutoff y
    let U : ℝ := nearTypeBound y / (y : ℝ)
    have hG : 1 ≤ G := by
      simpa only [G] using BoundedGaps.Maynard.one_le_log_natCast hy
    have hT : T ≤ 2 * G ^ 40 := by
      simpa only [T, G, nearVaughanCutoff] using
        logPowerCutoff_le_two_log_pow (e := 40) hy
    have hU : 0 ≤ U := div_nonneg (nearTypeBound_nonneg y) (Nat.cast_nonneg _)
    have hsmall : G ^ 16 *
        ((T * (2 * G * nearTypeBound y) +
          T ^ 2 * (G * nearTypeBound y)) / (y : ℝ)) ≤ 8 * A y := by
      have hy0 : (y : ℝ) ≠ 0 := by exact_mod_cast (show y ≠ 0 by omega)
      rw [add_div]
      rw [show T * (2 * G * nearTypeBound y) / (y : ℝ) =
          T * (2 * G) * U by dsimp only [U]; field_simp,
        show T ^ 2 * (G * nearTypeBound y) / (y : ℝ) =
          T ^ 2 * G * U by dsimp only [U]; field_simp]
      change G ^ 16 * (T * (2 * G) * U + T ^ 2 * G * U) ≤
        8 * (G ^ 97 * U)
      have hfirst : G ^ 16 * (T * (2 * G) * U) ≤
          4 * G ^ 57 * U := by
        calc
          _ ≤ G ^ 16 * ((2 * G ^ 40) * (2 * G) * U) := by gcongr
          _ = 4 * G ^ 57 * U := by ring
      have hsecond : G ^ 16 * (T ^ 2 * G * U) ≤
          4 * G ^ 97 * U := by
        calc
          _ ≤ G ^ 16 * ((2 * G ^ 40) ^ 2 * G * U) := by gcongr
          _ = 4 * G ^ 97 * U := by ring
      have hp : G ^ 57 ≤ G ^ 97 := pow_le_pow_right₀ hG (by omega)
      calc
        _ = G ^ 16 * (T * (2 * G) * U) +
            G ^ 16 * (T ^ 2 * G * U) := by ring
        _ ≤ 4 * G ^ 57 * U + 4 * G ^ 97 * U := add_le_add hfirst hsecond
        _ ≤ 4 * G ^ 97 * U + 4 * G ^ 97 * U := by gcongr
        _ = 8 * (G ^ 97 * U) := by ring
    have hquarterSqrt : G ^ (1 / 4 : ℝ) ≤ Real.sqrt G := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hG (by norm_num)
    have hfourth := near_fourth_term_scaled_le hy
      (hquarter.trans hquarterSqrt)
    unfold nearChebyshevMajorant centralChebyshevMajorant
    norm_num only [Nat.cast_pow]
    change G ^ 16 * ((T * (2 * G * nearTypeBound y) +
        T ^ 2 * (G * nearTypeBound y) +
        ((dyadicExponentRange y).card : ℝ) ^ 2 *
          Real.sqrt (centralFourthUniformMajorant y
            (nearVaughanCutoff y) (centralUniformDelta y))) / (y : ℝ)) ≤ _
    rw [add_div]
    rw [mul_add]
    simpa only [G, B] using add_le_add hsmall hfourth
  have hupper : Tendsto (fun y : ℕ ↦ 8 * A y + B y) atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using hA.const_mul 8 |>.add hB
  exact squeeze_zero' (Eventually.of_forall hnonneg) hbound hupper

def farScaledError (y : ℕ) : ℝ :=
  Real.log (y : ℝ) ^ 6 *
    (Real.log (y : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * farFourthError y

lemma farScaledError_nonneg (y : ℕ) : 0 ≤ farScaledError y := by
  unfold farScaledError
  exact mul_nonneg (mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 6)
    (sq_nonneg _)) (farFourthError_nonneg y)

theorem tendsto_farScaledError_zero :
    Tendsto farScaledError atTop (nhds 0) := by
  have hinvSqrt : Tendsto (fun y : ℕ ↦
      (Real.sqrt (Real.log (y : ℝ)))⁻¹) atTop (nhds 0) := by
    have hlogTop : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    exact (Real.tendsto_sqrt_atTop.comp hlogTop).inv_tendsto_atTop
  have hupper : Tendsto (fun y : ℕ ↦
      104 * (Real.sqrt (Real.log (y : ℝ)))⁻¹ +
        Real.log (y : ℝ) ^ 7 * inverseSquareAsymptoticDelta y)
      atTop (nhds 0) := by
    have hdelta : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 7 *
        inverseSquareAsymptoticDelta y) atTop (nhds 0) := by
      have h100 : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 100 *
          inverseSquareAsymptoticDelta y) atTop (nhds 0) := by
        simpa only [inverseSquareAsymptoticDelta] using
          tendsto_log_pow_mul_inverseSquareUniformDelta_zero
      have hn : ∀ᶠ y : ℕ in atTop,
          0 ≤ Real.log (y : ℝ) ^ 7 * inverseSquareAsymptoticDelta y := by
        filter_upwards [eventually_ge_atTop 1] with y hy
        exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 7)
          (inverseSquareAsymptoticDelta_nonneg y)
      have hb : ∀ᶠ y : ℕ in atTop,
          Real.log (y : ℝ) ^ 7 * inverseSquareAsymptoticDelta y ≤
            Real.log (y : ℝ) ^ 100 * inverseSquareAsymptoticDelta y := by
        filter_upwards [eventually_ge_atTop 4] with y hy
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (one_le_log_natCast hy) (by omega))
          (inverseSquareAsymptoticDelta_nonneg y)
      exact squeeze_zero' hn hb h100
    simpa only [mul_zero, zero_add] using hinvSqrt.const_mul 104 |>.add hdelta
  have hbound : ∀ᶠ y : ℕ in atTop,
      farScaledError y ≤
        104 * (Real.sqrt (Real.log (y : ℝ)))⁻¹ +
          Real.log (y : ℝ) ^ 7 * inverseSquareAsymptoticDelta y := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    let G : ℝ := Real.log (y : ℝ)
    let T : ℝ := farVaughanCutoff y
    let H : ℝ := farSeparation y
    let R : ℝ := G ^ (1 / 4 : ℝ)
    have hG : 1 ≤ G := by simpa only [G] using one_le_log_natCast hy
    have hG0 : 0 ≤ G := zero_le_one.trans hG
    have hT : G ^ 7 < T := by
      simpa only [G, T, farVaughanCutoff] using
        (logPowerCutoff_real_bounds (e := 7) (show 1 ≤ y by omega)).1
    have hH : G ^ 8 < H := by
      simpa only [G, H, farSeparation] using
        (logPowerCutoff_real_bounds (e := 8) (show 1 ≤ y by omega)).1
    have hR : R ^ 2 = Real.sqrt G := by
      dsimp only [R]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hG0]
      norm_num [Real.sqrt_eq_rpow]
    have hcut : G ^ 6 * R ^ 2 * (6 / T) ≤ 6 * (Real.sqrt G)⁻¹ := by
      rw [hR]
      have hT0 : 0 < T := lt_of_lt_of_le (pow_pos (by positivity) 7) hT.le
      have hsqrt : 0 < Real.sqrt G := Real.sqrt_pos.2 (by positivity)
      rw [inv_eq_one_div]
      rw [show G ^ 6 * Real.sqrt G * (6 / T) =
          6 * (G ^ 6 * Real.sqrt G) / T by ring,
        show 6 * (1 / Real.sqrt G) = 6 / Real.sqrt G by ring]
      rw [div_le_div_iff₀ hT0 hsqrt]
      calc
        6 * (G ^ 6 * Real.sqrt G) * Real.sqrt G =
            6 * G ^ 6 * (Real.sqrt G) ^ 2 := by ring
        _ = 6 * G ^ 7 := by
          rw [Real.sq_sqrt hG0]
          ring
        _ ≤ 6 * T := by gcongr
    have hsep : G ^ 6 * R ^ 2 * (98 / H) ≤
        98 * (Real.sqrt G)⁻¹ := by
      rw [hR]
      have hH0 : 0 < H := lt_of_lt_of_le (pow_pos (by positivity) 8) hH.le
      have hTlike : G ^ 7 ≤ H := by
        calc G ^ 7 ≤ G ^ 8 := pow_le_pow_right₀ hG (by omega)
          _ ≤ H := hH.le
      have hsqrt : 0 < Real.sqrt G := Real.sqrt_pos.2 (by positivity)
      rw [inv_eq_one_div]
      rw [show G ^ 6 * Real.sqrt G * (98 / H) =
          98 * (G ^ 6 * Real.sqrt G) / H by ring,
        show 98 * (1 / Real.sqrt G) = 98 / Real.sqrt G by ring]
      rw [div_le_div_iff₀ hH0 hsqrt]
      calc
        98 * (G ^ 6 * Real.sqrt G) * Real.sqrt G =
            98 * G ^ 6 * (Real.sqrt G) ^ 2 := by ring
        _ = 98 * G ^ 7 := by
          rw [Real.sq_sqrt hG0]
          ring
        _ ≤ 98 * H := by gcongr
    have hRleG : R ^ 2 ≤ G := by
      rw [hR]
      have hs0 : 0 ≤ Real.sqrt G := Real.sqrt_nonneg G
      nlinarith [Real.sq_sqrt hG0]
    unfold farScaledError farFourthError
    change G ^ 6 * R ^ 2 *
      (6 / T + 98 / H + inverseSquareAsymptoticDelta y) ≤ _
    calc
      _ = G ^ 6 * R ^ 2 * (6 / T) +
          G ^ 6 * R ^ 2 * (98 / H) +
          G ^ 6 * R ^ 2 * inverseSquareAsymptoticDelta y := by ring
      _ ≤ 6 * (Real.sqrt G)⁻¹ + 98 * (Real.sqrt G)⁻¹ +
          G ^ 7 * inverseSquareAsymptoticDelta y := by
        exact add_le_add (add_le_add hcut hsep)
          (mul_le_mul_of_nonneg_right
            (by calc G ^ 6 * R ^ 2 ≤ G ^ 6 * G := by gcongr
                     _ = G ^ 7 := by ring)
            (inverseSquareAsymptoticDelta_nonneg y))
      _ = 104 * (Real.sqrt G)⁻¹ +
          G ^ 7 * inverseSquareAsymptoticDelta y := by ring
  exact squeeze_zero' (Eventually.of_forall farScaledError_nonneg) hbound hupper

def farFourthLimitConstant : ℝ := 16 * Real.sqrt 20

lemma far_fourth_term_div_le {y : ℕ} (hy : 4 ≤ y)
    (hlogT : Real.log (farVaughanCutoff y : ℝ) + 3 ≤
      Real.log (y : ℝ) ^ (1 / 4 : ℝ)) :
    ((dyadicExponentRange y).card : ℝ) ^ 2 *
        Real.sqrt (inverseSquareFourthUniformMajorant y
          (farVaughanCutoff y) (farSeparation y)
          (inverseSquareAsymptoticDelta y)) / (y : ℝ) ≤
      farFourthLimitConstant * Real.sqrt (farScaledError y) := by
  let Y : ℝ := y
  let G : ℝ := Real.log Y
  let T : ℝ := farVaughanCutoff y
  let R : ℝ := G ^ (1 / 4 : ℝ)
  let E : ℝ := farFourthError y
  let D : ℝ := Real.sqrt 20
  have hY : 0 < Y := by positivity
  have hG : 1 ≤ G := by simpa only [G, Y] using one_le_log_natCast hy
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hE : 0 ≤ E := by simpa only [E] using farFourthError_nonneg y
  have hlogTwo : Real.log (2 * Y) ≤ 2 * G := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hY.ne']
    have hlog2 : Real.log 2 ≤ G := Real.log_le_log (by norm_num) (by
      change (2 : ℝ) ≤ (y : ℝ); exact_mod_cast (show 2 ≤ y by omega))
    linarith
  have hlogTwo0 : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by
    change (1 : ℝ) ≤ 2 * (y : ℝ); exact_mod_cast (show 1 ≤ 2 * y by omega))
  have hlogT0 : 0 ≤ Real.log T + 3 := by
    have : (1 : ℝ) ≤ T := by
      change (1 : ℝ) ≤ (farVaughanCutoff y : ℝ)
      exact_mod_cast (show 1 ≤ logPowerCutoff 7 y by exact logPowerCutoff_pos 7 y)
    linarith [Real.log_nonneg this]
  have hR0 : 0 ≤ R := Real.rpow_nonneg hG0 _
  have hA : inverseSquareFourthUniformMajorant y
      (farVaughanCutoff y) (farSeparation y)
      (inverseSquareAsymptoticDelta y) ≤
        20 * Y ^ 2 * G ^ 2 * R ^ 2 * E := by
    unfold inverseSquareFourthUniformMajorant
    change (8 / 3 : ℝ) * Y ^ 2 * Real.log (2 * Y) ^ 2 *
      (Real.log T + 3) ^ 2 * E ≤ _
    calc
      _ ≤ (8 / 3 : ℝ) * Y ^ 2 * (2 * G) ^ 2 * R ^ 2 * E := by gcongr
      _ = (32 / 3 : ℝ) * Y ^ 2 * G ^ 2 * R ^ 2 * E := by ring
      _ ≤ 20 * Y ^ 2 * G ^ 2 * R ^ 2 * E := by
        have : 0 ≤ Y ^ 2 * G ^ 2 * R ^ 2 * E := by positivity
        nlinarith
  have hDsq : D ^ 2 = 20 := by
    dsimp only [D]; rw [Real.sq_sqrt]; norm_num
  have hsqrtA : Real.sqrt (inverseSquareFourthUniformMajorant y
      (farVaughanCutoff y) (farSeparation y)
      (inverseSquareAsymptoticDelta y)) ≤
      D * Y * Real.sqrt (G ^ 2 * R ^ 2 * E) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    calc
      _ ≤ 20 * Y ^ 2 * G ^ 2 * R ^ 2 * E := hA
      _ = (D * Y * Real.sqrt (G ^ 2 * R ^ 2 * E)) ^ 2 := by
        rw [mul_pow, mul_pow, hDsq, Real.sq_sqrt]
        · ring
        · positivity
  have hcard := card_dyadicExponentRange_le_four_log hy
  change ((dyadicExponentRange y).card : ℝ) ≤ 4 * G at hcard
  have hcardSq : ((dyadicExponentRange y).card : ℝ) ^ 2 ≤ 16 * G ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (dyadicExponentRange y).card by positivity]
  have hsqrtG4 : Real.sqrt (G ^ 4) = G ^ 2 := by
    rw [show G ^ 4 = (G ^ 2) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hG0 2)]
  have hsqrtSplit : Real.sqrt (G ^ 6 * R ^ 2 * E) =
      G ^ 2 * Real.sqrt (G ^ 2 * R ^ 2 * E) := by
    rw [show G ^ 6 * R ^ 2 * E = G ^ 4 * (G ^ 2 * R ^ 2 * E) by ring,
      Real.sqrt_mul (pow_nonneg hG0 4), hsqrtG4]
  change ((dyadicExponentRange y).card : ℝ) ^ 2 *
      Real.sqrt (inverseSquareFourthUniformMajorant y
        (farVaughanCutoff y) (farSeparation y)
        (inverseSquareAsymptoticDelta y)) / Y ≤
    16 * D * Real.sqrt (G ^ 6 * R ^ 2 * E)
  calc
    _ ≤ (16 * G ^ 2) *
        (D * Y * Real.sqrt (G ^ 2 * R ^ 2 * E)) / Y := by gcongr
    _ = 16 * D * (G ^ 2 * Real.sqrt (G ^ 2 * R ^ 2 * E)) := by field_simp
    _ = _ := by rw [hsqrtSplit]

theorem tendsto_farChebyshevMajorant_div_zero :
    Tendsto (fun y : ℕ ↦ farChebyshevMajorant y / (y : ℝ))
      atTop (nhds 0) := by
  let A : ℕ → ℝ := fun y ↦ Real.log (y : ℝ) ^ 15 *
    (farTypeBound y / (y : ℝ))
  let B : ℕ → ℝ := fun y ↦ farFourthLimitConstant *
    Real.sqrt (farScaledError y)
  have hA : Tendsto A atTop (nhds 0) :=
    tendsto_log_15_mul_farTypeBound_div_zero
  have hB : Tendsto B atTop (nhds 0) := by
    have hs := tendsto_farScaledError_zero.sqrt
    simpa only [B, Real.sqrt_zero, mul_zero] using hs.const_mul farFourthLimitConstant
  have hlog := eventually_log_logPowerCutoff_add_three_le 7
  have hn : ∀ y : ℕ, 0 ≤ farChebyshevMajorant y / (y : ℝ) := by
    intro y
    unfold farChebyshevMajorant inverseSquareChebyshevMajorant
    exact div_nonneg (by
      exact add_nonneg (add_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
          (mul_nonneg (by norm_num) (Real.log_natCast_nonneg y))
          (farTypeBound_nonneg y)))
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
          (Real.log_natCast_nonneg y) (farTypeBound_nonneg y))))
        (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))) (Nat.cast_nonneg _)
  have hb : ∀ᶠ y : ℕ in atTop,
      farChebyshevMajorant y / (y : ℝ) ≤ 8 * A y + B y := by
    filter_upwards [eventually_ge_atTop 4, hlog] with y hy hlogT
    let G : ℝ := Real.log (y : ℝ)
    let T : ℝ := farVaughanCutoff y
    let U : ℝ := farTypeBound y / (y : ℝ)
    have hG : 1 ≤ G := by simpa only [G] using one_le_log_natCast hy
    have hT : T ≤ 2 * G ^ 7 := by
      simpa only [T, G, farVaughanCutoff] using
        logPowerCutoff_le_two_log_pow (e := 7) hy
    have hU : 0 ≤ U := div_nonneg (farTypeBound_nonneg y) (Nat.cast_nonneg _)
    have hsmall : (T * (2 * G * farTypeBound y) +
        T ^ 2 * (G * farTypeBound y)) / (y : ℝ) ≤ 8 * A y := by
      have hy0 : (y : ℝ) ≠ 0 := by exact_mod_cast (show y ≠ 0 by omega)
      rw [add_div]
      rw [show T * (2 * G * farTypeBound y) / (y : ℝ) =
          T * (2 * G) * U by dsimp only [U]; field_simp,
        show T ^ 2 * (G * farTypeBound y) / (y : ℝ) =
          T ^ 2 * G * U by dsimp only [U]; field_simp]
      change T * (2 * G) * U + T ^ 2 * G * U ≤ 8 * (G ^ 15 * U)
      calc
        _ ≤ 4 * G ^ 8 * U + 4 * G ^ 15 * U := by
          apply add_le_add
          · calc _ ≤ (2 * G ^ 7) * (2 * G) * U := by gcongr
                 _ = 4 * G ^ 8 * U := by ring
          · calc _ ≤ (2 * G ^ 7) ^ 2 * G * U := by gcongr
                 _ = 4 * G ^ 15 * U := by ring
        _ ≤ 4 * G ^ 15 * U + 4 * G ^ 15 * U := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ hG (by omega : 8 ≤ 15)) (by norm_num)) hU)
            le_rfl
        _ = 8 * (G ^ 15 * U) := by ring
    have hfourth := far_fourth_term_div_le hy hlogT
    unfold farChebyshevMajorant inverseSquareChebyshevMajorant
    norm_num only [Nat.cast_pow]
    change (T * (2 * G * farTypeBound y) +
        T ^ 2 * (G * farTypeBound y) +
        ((dyadicExponentRange y).card : ℝ) ^ 2 *
          Real.sqrt (inverseSquareFourthUniformMajorant y
            (farVaughanCutoff y) (farSeparation y)
            (inverseSquareAsymptoticDelta y))) / (y : ℝ) ≤ _
    rw [add_div]
    simpa only [B] using add_le_add hsmall hfourth
  have hu : Tendsto (fun y : ℕ ↦ 8 * A y + B y) atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using hA.const_mul 8 |>.add hB
  exact squeeze_zero' (Eventually.of_forall hn) hb hu

theorem eventually_nearVaughanCutoff_le_baseShift :
    ∀ᶠ y : ℕ in atTop, nearVaughanCutoff y ≤ baseShift y := by
  have hratio := tendsto_logarithmicSafety_pow_div_baseShift 1
  have hsmall : ∀ᶠ y : ℕ in atTop,
      2 * (logarithmicSafety y / (baseShift y : ℝ)) ≤ 1 :=
    by simpa only [pow_one] using
      (hratio.const_mul 2).eventually
        (Iic_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1))
  filter_upwards [hsmall, eventually_ge_atTop 4,
    CentralAsymptotic.tendsto_baseShift_atTop.eventually
      (eventually_ge_atTop 1)] with y hsmall hy hb
  let G : ℝ := Real.log (y : ℝ)
  have hG : 1 ≤ G := by simpa only [G] using one_le_log_natCast hy
  have hcut : (nearVaughanCutoff y : ℝ) ≤ 2 * G ^ 40 := by
    simpa only [nearVaughanCutoff, G] using
      logPowerCutoff_le_two_log_pow (e := 40) hy
  have hp : G ^ 40 ≤ logarithmicSafety y := by
    unfold logarithmicSafety
    exact (pow_le_pow_left₀ (zero_le_one.trans hG) (by linarith) 40).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ G + 2) (by omega))
  have hb0 : (0 : ℝ) < baseShift y := by exact_mod_cast (show 0 < baseShift y by omega)
  have hreal : (nearVaughanCutoff y : ℝ) ≤ baseShift y := by
    calc
      _ ≤ 2 * G ^ 40 := hcut
      _ ≤ 2 * logarithmicSafety y := by gcongr
      _ ≤ (baseShift y : ℝ) := by
        have hdiv : (2 * logarithmicSafety y) / (baseShift y : ℝ) ≤ 1 := by
          calc
            (2 * logarithmicSafety y) / (baseShift y : ℝ) =
                2 * (logarithmicSafety y / (baseShift y : ℝ)) := by ring
            _ ≤ 1 := hsmall
        exact (div_le_one hb0).mp hdiv
  exact_mod_cast hreal

theorem eventually_near_basic_parameters :
    ∀ᶠ y : ℕ in atTop,
      2 * nearVaughanCutoff y ^ 4 ≤ y ∧
      2 * nearVaughanCutoff y ^ 2 * inverseSquareUniformScale y ≤ y ∧
      8 * inverseSquareUniformScale y ^ 2 ≤ y := by
  have hbaseLarge : ∀ᶠ y : ℕ in atTop, 2 ≤ baseShift y :=
    CentralAsymptotic.tendsto_baseShift_atTop.eventually (eventually_ge_atTop 2)
  filter_upwards [eventually_nearVaughanCutoff_le_baseShift,
    hbaseLarge, eventually_inverseSquare_basic_parameters] with y hTb hb hbasic
  let T := nearVaughanCutoff y
  let q := baseShift y
  let Z := inverseSquareUniformScale y
  have hq16 : q ^ 16 ≤ y := baseShift_pow_sixteen_le y
  have hZ : Z ≤ 2 * q := by dsimp only [Z, inverseSquareUniformScale, q]; omega
  have hfirst : 2 * T ^ 4 ≤ y := by
    calc
      2 * T ^ 4 ≤ 2 * q ^ 4 := by gcongr
      _ ≤ q ^ 16 := by
        have : 2 ≤ q ^ 12 := by
          calc 2 ≤ 2 ^ 12 := by norm_num
            _ ≤ q ^ 12 := Nat.pow_le_pow_left hb 12
        calc
          2 * q ^ 4 ≤ q ^ 12 * q ^ 4 := Nat.mul_le_mul_right _ this
          _ = q ^ 16 := by ring
      _ ≤ y := hq16
  have hsecond : 2 * T ^ 2 * Z ≤ y := by
    calc
      2 * T ^ 2 * Z ≤ 4 * q ^ 3 := by
        calc
          2 * T ^ 2 * Z ≤ 2 * q ^ 2 * (2 * q) := by gcongr
          _ = 4 * q ^ 3 := by ring
      _ ≤ q ^ 16 := by
        have : 4 ≤ q ^ 13 := by
          calc 4 ≤ 2 ^ 13 := by norm_num
            _ ≤ q ^ 13 := Nat.pow_le_pow_left hb 13
        calc
          4 * q ^ 3 ≤ q ^ 13 * q ^ 3 := Nat.mul_le_mul_right _ this
          _ = q ^ 16 := by ring
      _ ≤ y := hq16
  exact ⟨hfirst, hsecond, hbasic.2.2⟩

theorem eventually_nearChebyshev_bound :
    ∀ᶠ y : ℕ in atTop, ∀ {x : ℕ} {X : ℝ},
      x < y → y ≤ 2 * x → 0 < X →
      (y : ℝ) ^ 2 ≤ 4 * X → X ≤ (y : ℝ) ^ 16 →
      ‖weightedChebyshevInterval (reciprocalWeight X) x y‖ ≤
        nearChebyshevMajorant y := by
  have hsizeEvent := eventually_centralCorrelationSizeCondition
  rcases hsizeEvent.exists_forall_of_atTop with ⟨M₀, hM₀⟩
  have hZlarge : ∀ᶠ y : ℕ in atTop, M₀ ≤ inverseSquareUniformScale y :=
    tendsto_inverseSquareUniformScale_atTop.eventually (eventually_ge_atTop M₀)
  filter_upwards [eventually_ge_atTop 4, eventually_near_basic_parameters,
    hZlarge] with y hy hbasic hZlargeY
  intro x X hxy hyx hX hXlo hXhi
  let T := nearVaughanCutoff y
  let Z := inverseSquareUniformScale y
  let delta := centralUniformDelta y
  let B := nearTypeBound y
  have hT : 0 < T := by exact logPowerCutoff_pos 40 y
  have hZ : 1 ≤ Z := by dsimp only [Z, inverseSquareUniformScale]; omega
  have hdelta : 0 ≤ delta := by
    simpa only [delta] using centralUniformDelta_nonneg y
  have hB : 0 ≤ B := by simpa only [B] using nearTypeBound_nonneg y
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
    dsimp only [B, nearTypeBound, delta]
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

lemma farVaughanCutoff_le_reciprocalVaughanCutoff {y : ℕ} (hy : 4 ≤ y) :
    farVaughanCutoff y ≤ reciprocalVaughanCutoff y := by
  unfold farVaughanCutoff logPowerCutoff reciprocalVaughanCutoff
  apply Nat.add_le_add_right
  apply Nat.floor_mono
  have hG : 1 ≤ Real.log (y : ℝ) := one_le_log_natCast hy
  exact pow_le_pow_right₀ hG (by omega)

theorem eventually_farChebyshev_bound :
    ∀ᶠ y : ℕ in atTop, ∀ {x : ℕ} {X : ℝ},
      x < y → y ≤ 2 * x → 0 < X →
      (y : ℝ) ^ 2 ≤ 4 * X → X ≤ (y : ℝ) ^ 16 →
      (farSeparation y : ℝ) ^ 2 * (y : ℝ) ^ 2 ≤ X →
      ‖weightedChebyshevInterval (inverseSquareWeight X) x y‖ ≤
        farChebyshevMajorant y := by
  have hsizeEvent := eventually_inverseSquareCorrelationSizeCondition
  rcases hsizeEvent.exists_forall_of_atTop with ⟨M₀, hM₀⟩
  have hZlarge : ∀ᶠ y : ℕ in atTop, M₀ ≤ inverseSquareUniformScale y :=
    tendsto_inverseSquareUniformScale_atTop.eventually (eventually_ge_atTop M₀)
  have hCtwo : ∀ᶠ y : ℕ in atTop, 2 ≤ inverseSquareCorrelationCap y :=
    tendsto_inverseSquareCorrelationCap_atTop.eventually (eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop 4, eventually_inverseSquare_basic_parameters,
    eventually_correlationCap_sq_le_uniformScale, hZlarge, hCtwo] with
      y hy hbasic hCZ hZlargeY hCtwoY
  intro x X hxy hyx hX hXlo hXhi hXratio
  let T := farVaughanCutoff y
  let H := farSeparation y
  let C := inverseSquareCorrelationCap y
  let Z := inverseSquareUniformScale y
  let delta := inverseSquareAsymptoticDelta y
  let B := farTypeBound y
  have hT : 0 < T := logPowerCutoff_pos 7 y
  have hH : 0 < H := logPowerCutoff_pos 8 y
  have hC : 2 ≤ C := by simpa only [C] using hCtwoY
  have hZ : 1 ≤ Z := by dsimp only [Z, inverseSquareUniformScale]; omega
  have hdelta : 0 ≤ delta := by
    simpa only [delta] using inverseSquareAsymptoticDelta_nonneg y
  have hB : 0 ≤ B := by simpa only [B] using farTypeBound_nonneg y
  have hTold : T ≤ reciprocalVaughanCutoff y :=
    farVaughanCutoff_le_reciprocalVaughanCutoff hy
  have hTy : T ≤ y := by
    have hOldPos := reciprocalVaughanCutoff_pos y
    have hTone : reciprocalVaughanCutoff y ≤ reciprocalVaughanCutoff y ^ 4 := by
      nlinarith [show 1 ≤ reciprocalVaughanCutoff y ^ 2 by
        exact one_le_pow₀ hOldPos]
    exact hTold.trans (hTone.trans
      ((show reciprocalVaughanCutoff y ^ 4 ≤
        2 * reciprocalVaughanCutoff y ^ 4 by omega).trans hbasic.1))
  have hTx : T ^ 4 ≤ x := by
    have hpow : T ^ 4 ≤ reciprocalVaughanCutoff y ^ 4 := by gcongr
    have htwo : 2 * reciprocalVaughanCutoff y ^ 4 ≤ 2 * x :=
      hbasic.1.trans hyx
    exact hpow.trans (by omega)
  have hsmallM : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      Z ≤ x / q + 1 ∧ x / q + 1 ≤ y := by
    intro q hq hqT
    have hqOld : q ≤ reciprocalVaughanCutoff y ^ 2 :=
      hqT.trans (by gcongr)
    have hcore : reciprocalVaughanCutoff y ^ 2 * Z ≤ x := by
      have htwo : 2 * (reciprocalVaughanCutoff y ^ 2 * Z) ≤ 2 * x := by
        simpa [mul_assoc] using hbasic.2.1.trans hyx
      omega
    have hqZ : q * Z ≤ x := (Nat.mul_le_mul_right Z hqOld).trans hcore
    have hZdiv : Z ≤ x / q := (Nat.le_div_iff_mul_le (by omega)).2 (by
      simpa [Nat.mul_comm] using hqZ)
    exact ⟨hZdiv.trans (Nat.le_add_right _ _), by
      have := Nat.div_le_self x q
      omega⟩
  have hsmallSize : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      inverseSquareCorrelationSizeCondition (x / q + 1) := by
    intro q hq hqT
    exact hM₀ _ (hZlargeY.trans (hsmallM q hq hqT).1)
  have hsmallCap : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      baseShift (x / q + 1) ≤ (x / q + 1) / C := by
    intro q hq hqT
    exact baseShift_le_div_of_sq_le (by omega)
      (hCZ.trans (hsmallM q hq hqT).1)
  have hsmallEnvelope : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      ∀ Q : ℝ, 0 < Q → ((x / q + 1 : ℕ) : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * ((x / q + 1 : ℕ) : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q (x / q + 1) C ≤
        delta * (x / q + 1 : ℕ) := by
    intro q hq hqT Q hQ hQlo hQhi
    have hM := hsmallM q hq hqT
    apply cappedInverseSquareCorrelationEnvelope_le_uniform hQ hZ hM.1 hM.2 hC
      (hsmallSize q hq hqT) (hsmallCap q hq hqT) hQlo hQhi
  have hsmallB : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      inverseSquareOneDimensionalBound (x / q + 1) H delta ≤ B := by
    intro q hq hqT
    have hM := (hsmallM q hq hqT).2
    unfold inverseSquareOneDimensionalBound
    dsimp only [B, farTypeBound, H, delta]
    gcongr
  have hlargeM : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y → Z ≤ L ∧ L ≤ y := by
    intro L hxL hLy
    have hfour : 4 * Z ^ 2 ≤ x := by
      have htwo : 8 * Z ^ 2 ≤ 2 * x := hbasic.2.2.trans hyx
      omega
    have hsq : Z ^ 2 < L ^ 2 := by nlinarith
    have hZL : Z ≤ L := by nlinarith
    exact ⟨hZL, hLy⟩
  have hlargeSize : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      inverseSquareCentralCorrelationSizeCondition L := by
    intro L hxL hLy
    exact hM₀ _ (hZlargeY.trans (hlargeM L hxL hLy).1)
  have hlargeCap : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      baseShift L ≤ L / C := by
    intro L hxL hLy
    exact baseShift_le_div_of_sq_le (by omega)
      (hCZ.trans (hlargeM L hxL hLy).1)
  have hlargeEnvelope : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      ∀ Q : ℝ, 0 < Q → (L : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * (L : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q L C ≤ delta * L := by
    intro L hxL hLy Q hQ hQlo hQhi
    have hM := hlargeM L hxL hLy
    apply cappedInverseSquareCorrelationEnvelope_le_uniform hQ hZ hM.1 hM.2 hC
      (hlargeSize L hxL hLy) (hlargeCap L hxL hLy) hQlo hQhi
  apply norm_weightedChebyshevInterval_inverseSquare_le hX hT hH hdelta
    hTy hTx hxy hXlo hyx hXhi hXratio hC hB
    hsmallSize hsmallCap hsmallEnvelope hsmallB
    hlargeSize hlargeCap hlargeEnvelope

def nearPrimeMajorant (y : ℕ) : ℝ :=
  nearChebyshevMajorant y +
    (Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ))

def farPrimeMajorant (y : ℕ) : ℝ :=
  farChebyshevMajorant y +
    (Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ))

theorem tendsto_primePowerCorrection_scaled_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 16 *
      ((Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ)) / (y : ℝ)))
      atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcReal := Erdos49.Analytic.eventually_psi_sub_theta_div_log_pow
    16 (show 0 < ε / 2 by positivity)
  have hcNat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hcReal
  filter_upwards [hcNat, eventually_gt_atTop 1] with y hc hy
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg]
  · have hG : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast hy)
    have hyR : (0 : ℝ) < y := by positivity
    have hpow : 0 < Real.log (y : ℝ) ^ 16 := pow_pos hG 16
    have hcorr0 : 0 ≤ Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ) :=
      sub_nonneg.mpr (Chebyshev.theta_le_psi _)
    calc
      Real.log (y : ℝ) ^ 16 *
          ((Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ)) / (y : ℝ)) ≤
        Real.log (y : ℝ) ^ 16 *
          (((ε / 2) * (y : ℝ) / Real.log (y : ℝ) ^ 16) / (y : ℝ)) := by
            gcongr
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  · exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 16)
      (div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))
        (Nat.cast_nonneg _))

theorem tendsto_nearPrimeMajorant_scaled_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 16 *
      (nearPrimeMajorant y / (y : ℝ))) atTop (nhds 0) := by
  unfold nearPrimeMajorant
  have h := tendsto_nearChebyshevMajorant_scaled_zero.add
    tendsto_primePowerCorrection_scaled_zero
  convert h using 1
  · funext y
    by_cases hy : y = 0
    · simp [hy]
    rw [add_div, mul_add]
  · norm_num

theorem tendsto_farPrimeMajorant_div_zero :
    Tendsto (fun y : ℕ ↦ farPrimeMajorant y / (y : ℝ))
      atTop (nhds 0) := by
  have hcorr : Tendsto (fun y : ℕ ↦
      (Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ)) / (y : ℝ))
      atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hcReal := Erdos49.Analytic.eventually_psi_sub_theta_div_log_pow
      0 (show 0 < ε / 2 by positivity)
    have hcNat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hcReal
    filter_upwards [hcNat, eventually_gt_atTop 1] with y hc hy
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg]
    · have hyR : (0 : ℝ) < y := by positivity
      have hcorr0 : 0 ≤ Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ) :=
        sub_nonneg.mpr (Chebyshev.theta_le_psi _)
      calc
        (Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ)) / (y : ℝ) ≤
            (((ε / 2) * (y : ℝ) / Real.log (y : ℝ) ^ 0) / (y : ℝ)) := by
              gcongr
        _ = ε / 2 := by field_simp
        _ < ε := by linarith
    · exact div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))
        (Nat.cast_nonneg _)
  unfold farPrimeMajorant
  convert tendsto_farChebyshevMajorant_div_zero.add hcorr using 1
  · funext y
    rw [add_div]
  · norm_num

theorem eventually_nearPrime_bound :
    ∀ᶠ y : ℕ in atTop, ∀ {x : ℕ} {X : ℝ},
      x < y → y ≤ 2 * x → 0 < X →
      (y : ℝ) ^ 2 ≤ 4 * X → X ≤ (y : ℝ) ^ 16 →
      ‖primeWeightedInterval (reciprocalWeight X) x y‖ ≤
        nearPrimeMajorant y := by
  filter_upwards [eventually_nearChebyshev_bound] with y hy
  intro x X hxy hyx hX hXlo hXhi
  apply norm_primeWeightedInterval_le
  · intro n
    simp
  · exact hy hxy hyx hX hXlo hXhi

theorem eventually_farPrime_bound :
    ∀ᶠ y : ℕ in atTop, ∀ {x : ℕ} {X : ℝ},
      x < y → y ≤ 2 * x → 0 < X →
      (y : ℝ) ^ 2 ≤ 4 * X → X ≤ (y : ℝ) ^ 16 →
      (farSeparation y : ℝ) ^ 2 * (y : ℝ) ^ 2 ≤ X →
      ‖primeWeightedInterval (inverseSquareWeight X) x y‖ ≤
        farPrimeMajorant y := by
  filter_upwards [eventually_farChebyshev_bound] with y hy
  intro x X hxy hyx hX hXlo hXhi hratio
  apply norm_primeWeightedInterval_le
  · intro n
    simp
  · exact hy hxy hyx hX hXlo hXhi hratio

end

end HighIndexChebyshev
end Erdos378
