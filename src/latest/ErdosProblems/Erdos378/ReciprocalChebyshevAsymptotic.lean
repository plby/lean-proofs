/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.VaughanReciprocalFull
import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanPowers
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Asymptotic cancellation in reciprocal Chebyshev sums

The Vaughan cutoff is a sixteenth power of a logarithm and the differencing
length is a square root.  These choices leave ample room in every power
saving occurring in the finite estimate.
-/

open Filter
open scoped Topology

namespace Erdos378
namespace ReciprocalChebyshevAsymptotic

open BoundedGaps.Maynard
open VaughanReciprocalFull
open VaughanReciprocalEstimate
open ReciprocalIntervalEstimate

noncomputable section

noncomputable def reciprocalVaughanCutoff (y : ℕ) : ℕ :=
  Nat.floor ((Real.log (y : ℝ)) ^ 16) + 1

noncomputable def reciprocalDifferencingLength (y : ℕ) : ℕ :=
  Nat.floor (Real.sqrt (y : ℝ)) + 1

lemma reciprocalVaughanCutoff_pos (y : ℕ) :
    0 < reciprocalVaughanCutoff y := by
  unfold reciprocalVaughanCutoff
  omega

lemma reciprocalDifferencingLength_pos (y : ℕ) :
    0 < reciprocalDifferencingLength y := by
  unfold reciprocalDifferencingLength
  omega

lemma reciprocalVaughanCutoff_real_bounds {y : ℕ} (hy : 4 ≤ y) :
    (Real.log (y : ℝ)) ^ 16 < (reciprocalVaughanCutoff y : ℝ) ∧
      (reciprocalVaughanCutoff y : ℝ) ≤
        (Real.log (y : ℝ)) ^ 16 + 1 := by
  have hlog0 : 0 ≤ Real.log (y : ℝ) := Real.log_natCast_nonneg y
  constructor
  · simpa only [reciprocalVaughanCutoff, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one ((Real.log (y : ℝ)) ^ 16)
  · unfold reciprocalVaughanCutoff
    push_cast
    gcongr
    exact Nat.floor_le (by positivity)

lemma reciprocalDifferencingLength_real_bounds {y : ℕ} (hy : 1 ≤ y) :
    Real.sqrt (y : ℝ) < (reciprocalDifferencingLength y : ℝ) ∧
      (reciprocalDifferencingLength y : ℝ) ≤ Real.sqrt (y : ℝ) + 1 := by
  constructor
  · simpa only [reciprocalDifferencingLength, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (Real.sqrt (y : ℝ))
  · unfold reciprocalDifferencingLength
    push_cast
    gcongr
    exact Nat.floor_le (Real.sqrt_nonneg _)

lemma reciprocalDifferencingLength_le_two_sqrt {y : ℕ} (hy : 1 ≤ y) :
    (reciprocalDifferencingLength y : ℝ) ≤ 2 * Real.sqrt (y : ℝ) := by
  have hb := (reciprocalDifferencingLength_real_bounds hy).2
  have hs : (1 : ℝ) ≤ Real.sqrt (y : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hy
  linarith

lemma reciprocalVaughanCutoff_le_two_log_pow {y : ℕ} (hy : 4 ≤ y) :
    (reciprocalVaughanCutoff y : ℝ) ≤
      2 * (Real.log (y : ℝ)) ^ 16 := by
  have hb := (reciprocalVaughanCutoff_real_bounds hy).2
  have hlog := one_le_log_natCast hy
  have hp : (1 : ℝ) ≤ Real.log (y : ℝ) ^ 16 := one_le_pow₀ hlog
  linarith

lemma reciprocalVaughanCutoff_le_y_seventeen {y : ℕ} (hy : 4 ≤ y) :
    (reciprocalVaughanCutoff y : ℝ) ≤ (y : ℝ) ^ 17 := by
  have hcut := reciprocalVaughanCutoff_le_two_log_pow hy
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy.trans' (by norm_num)
  have hlogY : Real.log (y : ℝ) ≤ (y : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < y)
    linarith
  have hp := pow_le_pow_left₀ (Real.log_natCast_nonneg y) hlogY 16
  calc
    _ ≤ 2 * Real.log (y : ℝ) ^ 16 := hcut
    _ ≤ 2 * (y : ℝ) ^ 16 := by gcongr
    _ ≤ (y : ℝ) * (y : ℝ) ^ 16 := by gcongr
    _ = (y : ℝ) ^ 17 := by ring

lemma log_reciprocalVaughanCutoff_le {y : ℕ} (hy : 4 ≤ y) :
    Real.log (reciprocalVaughanCutoff y : ℝ) ≤
      17 * Real.log (y : ℝ) := by
  have hcutpos : (0 : ℝ) < reciprocalVaughanCutoff y := by
    exact_mod_cast reciprocalVaughanCutoff_pos y
  have h := Real.log_le_log hcutpos (reciprocalVaughanCutoff_le_y_seventeen hy)
  rw [Real.log_pow] at h
  norm_num at h ⊢
  exact h

lemma card_dyadicExponentRange_le_four_log {y : ℕ} (hy : 4 ≤ y) :
    ((dyadicExponentRange y).card : ℝ) ≤ 4 * Real.log (y : ℝ) := by
  have hbase := card_dyadicExponentRange_le_log (show 0 < y by omega)
  have hlogy : Real.log 2 ≤ Real.log (y : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ y by omega))
  have hnum : Real.log (2 * (y : ℝ)) ≤ 2 * Real.log (y : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (y : ℝ) ≠ 0)]
    linarith
  have hden : (1 / Real.log 2 : ℝ) < 2 := by
    rw [div_lt_iff₀ (Real.log_pos (by norm_num))]
    nlinarith [Real.log_two_gt_d9]
  calc
    _ ≤ Real.log (2 * (y : ℝ)) / Real.log 2 := hbase
    _ ≤ (2 * Real.log (y : ℝ)) / Real.log 2 := by gcongr
    _ ≤ 4 * Real.log (y : ℝ) := by
      rw [div_eq_mul_inv]
      have hlog0 := Real.log_natCast_nonneg y
      calc
        2 * Real.log (y : ℝ) * (Real.log 2)⁻¹ ≤
            2 * Real.log (y : ℝ) * 2 := by
          apply mul_le_mul_of_nonneg_left
          · simpa only [one_div] using hden.le
          · positivity
        _ = 4 * Real.log (y : ℝ) := by ring

/-- The Type-I majorant after division by the square of its ambient
endpoint. -/
lemma reciprocalIntervalMajorant_le_log_sqrt_envelope {y : ℕ} (hy : 4 ≤ y) :
    reciprocalIntervalMajorant y (reciprocalDifferencingLength y) ≤
      400 * (y : ℝ) * Real.sqrt (y : ℝ) * Real.log (y : ℝ) := by
  let Y : ℝ := y
  let L : ℝ := reciprocalDifferencingLength y
  have hY : (4 : ℝ) ≤ Y := by
    change (4 : ℝ) ≤ (y : ℝ)
    exact_mod_cast hy
  have hlog : 1 ≤ Real.log Y := by simpa only [Y] using one_le_log_natCast hy
  have hsqrt : 1 ≤ Real.sqrt Y := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  have hLlo : Real.sqrt Y ≤ L := by
    exact (reciprocalDifferencingLength_real_bounds (show 1 ≤ y by omega)).1.le
  have hLhi : L ≤ 2 * Real.sqrt Y :=
    reciprocalDifferencingLength_le_two_sqrt (show 1 ≤ y by omega)
  have hLpos : 0 < L := lt_of_lt_of_le (Real.sqrt_pos.2 (by positivity)) hLlo
  have hdiv : Y / L ≤ Real.sqrt Y := by
    apply (div_le_iff₀ hLpos).2
    calc
      Y = Real.sqrt Y * Real.sqrt Y := by
        rw [Real.mul_self_sqrt (by positivity)]
      _ ≤ Real.sqrt Y * L := by gcongr
  unfold reciprocalIntervalMajorant
  change 2 * Y ^ 2 / L + 4 * Y * (L + 24 * Y * (1 + Real.log Y)) / L ≤ _
  have hfirst : 2 * Y ^ 2 / L ≤ 2 * Y * Real.sqrt Y := by
    calc
      2 * Y ^ 2 / L = 2 * Y * (Y / L) := by field_simp
      _ ≤ 2 * Y * Real.sqrt Y := by gcongr
  have hsecond : 4 * Y * L / L = 4 * Y := by field_simp
  have hthird : 96 * Y ^ 2 * (1 + Real.log Y) / L ≤
      192 * Y * Real.sqrt Y * Real.log Y := by
    calc
      _ = 96 * Y * (Y / L) * (1 + Real.log Y) := by field_simp
      _ ≤ 96 * Y * Real.sqrt Y * (1 + Real.log Y) := by gcongr
      _ ≤ 96 * Y * Real.sqrt Y * (2 * Real.log Y) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 192 * Y * Real.sqrt Y * Real.log Y := by ring
  calc
    _ = 2 * Y ^ 2 / L + 4 * Y * L / L +
        96 * Y ^ 2 * (1 + Real.log Y) / L := by ring
    _ ≤ 2 * Y * Real.sqrt Y + 4 * Y +
        192 * Y * Real.sqrt Y * Real.log Y :=
      add_le_add (add_le_add hfirst hsecond.le) hthird
    _ ≤ 400 * Y * Real.sqrt Y * Real.log Y := by
      have hA : Y ≤ Y * Real.sqrt Y * Real.log Y := by
        calc
          Y = Y * 1 * 1 := by ring
          _ ≤ Y * Real.sqrt Y * Real.log Y := by gcongr
      have hB : Y * Real.sqrt Y ≤ Y * Real.sqrt Y * Real.log Y := by
        calc
          Y * Real.sqrt Y = Y * Real.sqrt Y * 1 := by ring
          _ ≤ Y * Real.sqrt Y * Real.log Y := by gcongr
      nlinarith

lemma eventually_log_natCast_le_rpow (s : ℝ) (hs : 0 < s) :
    ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ≤ (y : ℝ) ^ s := by
  have hlittle :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hs).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := hlittle.bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hbound, eventually_ge_atTop 1] with y hybound hy
  have hlog : 0 ≤ Real.log (y : ℝ) := Real.log_natCast_nonneg y
  have hpow : 0 ≤ (y : ℝ) ^ s := Real.rpow_nonneg (by positivity) _
  simpa only [Function.comp_apply, one_mul, Real.norm_eq_abs,
    abs_of_nonneg hlog, abs_of_nonneg hpow, Real.rpow_one] using hybound

lemma eventually_log_natCast_rpow_le_rpow (a s : ℝ) (ha : 0 ≤ a)
    (hs : 0 < s) :
    ∀ᶠ y : ℕ in atTop,
      (Real.log (y : ℝ)) ^ a ≤ (y : ℝ) ^ s := by
  have hlittle :=
    (isLittleO_log_rpow_rpow_atTop a hs).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := hlittle.bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hbound, eventually_ge_atTop 1] with y hybound hy
  have hlog : 0 ≤ Real.log (y : ℝ) := Real.log_natCast_nonneg y
  have hleft : 0 ≤ (Real.log (y : ℝ)) ^ a := Real.rpow_nonneg hlog _
  have hright : 0 ≤ (y : ℝ) ^ s := Real.rpow_nonneg (by positivity) _
  simpa only [Function.comp_apply, one_mul, Real.norm_eq_abs,
    abs_of_nonneg hleft, abs_of_nonneg hright] using hybound

lemma tendsto_log_natCast_rpow_div_rpow (a s : ℝ) (hs : 0 < s) :
    Tendsto (fun y : ℕ ↦
      (Real.log (y : ℝ)) ^ a / (y : ℝ) ^ s) atTop (nhds 0) := by
  exact ((isLittleO_log_rpow_rpow_atTop a hs).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

lemma reciprocalTypeIMajorant_le_rpow_envelope {y : ℕ} (hy : 4 ≤ y)
    (hlog : Real.log (y : ℝ) ≤ (y : ℝ) ^ (1 / 8 : ℝ)) :
    reciprocalTypeIMajorant y (reciprocalDifferencingLength y) ≤
      22 * (y : ℝ) ^ (13 / 16 : ℝ) := by
  let Y : ℝ := y
  have hYpos : 0 < Y := by positivity
  have hYone : 1 ≤ Y := by
    change (1 : ℝ) ≤ (y : ℝ)
    exact_mod_cast (show 1 ≤ y by omega)
  have hsqrtY : Real.sqrt Y = Y ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow Y
  have hprod : Y * Real.sqrt Y * Real.log Y ≤ Y ^ (13 / 8 : ℝ) := by
    calc
      Y * Real.sqrt Y * Real.log Y ≤
          Y * (Y ^ (1 / 2 : ℝ)) * (Y ^ (1 / 8 : ℝ)) := by
        rw [hsqrtY]
        gcongr
      _ = Y ^ (13 / 8 : ℝ) := by
        calc
          Y * Y ^ (1 / 2 : ℝ) * Y ^ (1 / 8 : ℝ) =
              Y ^ (3 / 2 : ℝ) * Y ^ (1 / 8 : ℝ) := by
            congr 1
            rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
              Real.rpow_add_one hYpos.ne']
            ring
          _ = Y ^ (13 / 8 : ℝ) := by
            rw [← Real.rpow_add hYpos]
            norm_num
  have hR : reciprocalIntervalMajorant y (reciprocalDifferencingLength y) ≤
      400 * Y ^ (13 / 8 : ℝ) := by
    calc
      _ ≤ 400 * Y * Real.sqrt Y * Real.log Y :=
        reciprocalIntervalMajorant_le_log_sqrt_envelope hy
      _ = 400 * (Y * Real.sqrt Y * Real.log Y) := by ring
      _ ≤ 400 * Y ^ (13 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
  have hsqrtR : Real.sqrt
      (reciprocalIntervalMajorant y (reciprocalDifferencingLength y)) ≤
      20 * Y ^ (13 / 16 : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    calc
      _ ≤ 400 * Y ^ (13 / 8 : ℝ) := hR
      _ = (20 * Y ^ (13 / 16 : ℝ)) ^ 2 := by
        have hp : (Y ^ (13 / 16 : ℝ)) ^ 2 = Y ^ (13 / 8 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hYpos)]
          norm_num
        rw [mul_pow, hp]
        norm_num
  have hL : (reciprocalDifferencingLength y : ℝ) ≤
      2 * Y ^ (13 / 16 : ℝ) := by
    calc
      _ ≤ 2 * Real.sqrt Y := by
        simpa only [Y] using
          reciprocalDifferencingLength_le_two_sqrt (show 1 ≤ y by omega)
      _ = 2 * Y ^ (1 / 2 : ℝ) := by rw [hsqrtY]
      _ ≤ 2 * Y ^ (13 / 16 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hYone (by norm_num)) (by norm_num)
  unfold reciprocalTypeIMajorant
  change (reciprocalDifferencingLength y : ℝ) +
    Real.sqrt (reciprocalIntervalMajorant y (reciprocalDifferencingLength y)) ≤ _
  linarith

lemma reciprocalChebyshev_type_terms_le {y : ℕ} (hy : 4 ≤ y)
    (hlog : Real.log (y : ℝ) ≤ (y : ℝ) ^ (1 / 8 : ℝ)) :
    (reciprocalVaughanCutoff y : ℝ) *
          (2 * Real.log (y : ℝ) *
            reciprocalTypeIMajorant y (reciprocalDifferencingLength y)) +
        (((reciprocalVaughanCutoff y) ^ 2 : ℕ) : ℝ) *
          (Real.log (y : ℝ) *
            reciprocalTypeIMajorant y (reciprocalDifferencingLength y)) ≤
      176 * (Real.log (y : ℝ)) ^ 33 *
        (y : ℝ) ^ (13 / 16 : ℝ) := by
  let Y : ℝ := y
  let G : ℝ := Real.log Y
  let T : ℝ := reciprocalVaughanCutoff y
  let B : ℝ := reciprocalTypeIMajorant y (reciprocalDifferencingLength y)
  have hG : 1 ≤ G := by simpa only [G, Y] using one_le_log_natCast hy
  have hT : T ≤ 2 * G ^ 16 := by
    simpa only [T, G, Y] using reciprocalVaughanCutoff_le_two_log_pow hy
  have hB : B ≤ 22 * Y ^ (13 / 16 : ℝ) := by
    simpa only [B, Y] using reciprocalTypeIMajorant_le_rpow_envelope hy hlog
  have hT0 : 0 ≤ T := by positivity
  have hB0 : 0 ≤ B := reciprocalTypeIMajorant_nonneg
  have hG0 : 0 ≤ G := hG.trans' (by norm_num)
  have hYpow0 : 0 ≤ Y ^ (13 / 16 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hfirst : T * (2 * G * B) ≤
      88 * G ^ 17 * Y ^ (13 / 16 : ℝ) := by
    calc
      _ ≤ (2 * G ^ 16) * (2 * G * (22 * Y ^ (13 / 16 : ℝ))) := by
        gcongr
      _ = 88 * G ^ 17 * Y ^ (13 / 16 : ℝ) := by ring
  have hsecond : T ^ 2 * (G * B) ≤
      88 * G ^ 33 * Y ^ (13 / 16 : ℝ) := by
    calc
      _ ≤ (2 * G ^ 16) ^ 2 * (G * (22 * Y ^ (13 / 16 : ℝ))) := by
        gcongr
      _ = 88 * G ^ 33 * Y ^ (13 / 16 : ℝ) := by ring
  have hpow : G ^ 17 ≤ G ^ 33 := pow_le_pow_right₀ hG (by omega)
  have hmain : T * (2 * G * B) + T ^ 2 * (G * B) ≤
      176 * G ^ 33 * Y ^ (13 / 16 : ℝ) := by
    calc
      _ ≤ 88 * G ^ 17 * Y ^ (13 / 16 : ℝ) +
        88 * G ^ 33 * Y ^ (13 / 16 : ℝ) := add_le_add hfirst hsecond
      _ ≤ 88 * G ^ 33 * Y ^ (13 / 16 : ℝ) +
        88 * G ^ 33 * Y ^ (13 / 16 : ℝ) := by gcongr
      _ = 176 * G ^ 33 * Y ^ (13 / 16 : ℝ) := by ring
  simpa only [T, G, B, Y, Nat.cast_pow] using hmain

lemma tendsto_reciprocalChebyshev_type_envelope :
    Tendsto (fun y : ℕ ↦
      (176 * (Real.log (y : ℝ)) ^ 33 *
        (y : ℝ) ^ (13 / 16 : ℝ)) / (y : ℝ)) atTop (nhds 0) := by
  have hbase := tendsto_log_natCast_rpow_div_rpow
    (33 : ℝ) (3 / 16 : ℝ) (by norm_num)
  convert hbase.const_mul 176 using 1
  · funext y
    by_cases hy : y = 0
    · simp [hy]
    have hyR : (0 : ℝ) < y := by positivity
    rw [show (13 / 16 : ℝ) = 1 - 3 / 16 by norm_num,
      Real.rpow_sub hyR]
    rw [Real.rpow_one]
    field_simp
    exact (Real.rpow_natCast (Real.log (y : ℝ)) 33).symm
  · norm_num

noncomputable def reciprocalFourthEnvelopeConstant : ℝ :=
  Real.sqrt (5000 * (2 + reciprocalCorrelationRootConstant))

lemma reciprocalFourthEnvelopeConstant_nonneg :
    0 ≤ reciprocalFourthEnvelopeConstant := by
  unfold reciprocalFourthEnvelopeConstant
  positivity

lemma reciprocalChebyshev_fourth_term_le {y : ℕ} (hy : 4 ≤ y)
    (hlogpow : (Real.log (y : ℝ)) ^ 16 ≤
      (y : ℝ) ^ (1 / 128 : ℝ)) :
    ((dyadicExponentRange y).card : ℝ) ^ 2 *
        Real.sqrt (reciprocalVaughanBlockMajorant
          (reciprocalVaughanCutoff y) y (reciprocalVaughanCutoff y)) ≤
      16 * reciprocalFourthEnvelopeConstant * (y : ℝ) /
        (Real.log (y : ℝ)) ^ 4 := by
  let Y : ℝ := y
  let G : ℝ := Real.log Y
  let T : ℝ := reciprocalVaughanCutoff y
  let C : ℝ := reciprocalCorrelationRootConstant
  let D : ℝ := reciprocalFourthEnvelopeConstant
  have hYpos : 0 < Y := by positivity
  have hG : 1 ≤ G := by simpa only [G, Y] using one_le_log_natCast hy
  have hGpos : 0 < G := lt_of_lt_of_le (by norm_num) hG
  have hTpos : 0 < T := by
    change (0 : ℝ) < (reciprocalVaughanCutoff y : ℝ)
    exact_mod_cast reciprocalVaughanCutoff_pos y
  have hC : 0 ≤ C := reciprocalCorrelationRootConstant_nonneg
  have hD : 0 ≤ D := reciprocalFourthEnvelopeConstant_nonneg
  have hlogTwo : Real.log (2 * Y) ≤ 2 * G := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hYpos.ne']
    have hlog2 : Real.log 2 ≤ G :=
      Real.log_le_log (by norm_num) (by
        change (2 : ℝ) ≤ (y : ℝ)
        exact_mod_cast (show 2 ≤ y by omega))
    linarith
  have hlogT : Real.log T + 3 ≤ 20 * G := by
    have hbase := log_reciprocalVaughanCutoff_le hy
    change Real.log T ≤ 17 * G at hbase
    linarith
  have hGpowpos : 0 < G ^ 16 := pow_pos hGpos _
  have hTlower : G ^ 16 < T := by
    simpa only [T, G, Y] using (reciprocalVaughanCutoff_real_bounds hy).1
  have hYpowpos : 0 < Y ^ (1 / 128 : ℝ) := Real.rpow_pos_of_pos hYpos _
  have hdivT : Y / T ≤ Y / G ^ 16 := by
    exact div_le_div_of_nonneg_left hYpos.le hGpowpos hTlower.le
  have hdivPow : Y / Y ^ (1 / 128 : ℝ) ≤ Y / G ^ 16 := by
    exact div_le_div_of_nonneg_left hYpos.le hGpowpos hlogpow
  have hbracket : 2 * Y / T + C * (Y / Y ^ (1 / 128 : ℝ)) ≤
      (2 + C) * Y / G ^ 16 := by
    calc
      _ = 2 * (Y / T) + C * (Y / Y ^ (1 / 128 : ℝ)) := by ring
      _ ≤ 2 * (Y / G ^ 16) + C * (Y / G ^ 16) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hdivT (by norm_num))
          (mul_le_mul_of_nonneg_left hdivPow hC)
      _ = (2 + C) * Y / G ^ 16 := by ring
  have hYone : (1 : ℝ) ≤ Y := by
    change (1 : ℝ) ≤ (y : ℝ)
    exact_mod_cast (show 1 ≤ y by omega)
  have hlogTwo0 : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by nlinarith)
  have hlogT3zero : 0 ≤ Real.log T + 3 := by
    have hlogTzero : 0 ≤ Real.log T := Real.log_nonneg (by
      change (1 : ℝ) ≤ (reciprocalVaughanCutoff y : ℝ)
      exact_mod_cast reciprocalVaughanCutoff_pos y)
    linarith
  have hA : reciprocalVaughanBlockMajorant T y (reciprocalVaughanCutoff y) ≤
      5000 * (2 + C) * Y ^ 2 / G ^ 12 := by
    unfold reciprocalVaughanBlockMajorant
    change (8 / 3 : ℝ) * Y * (Real.log (2 * Y)) ^ 2 *
      (Real.log T + 3) ^ 2 *
        (2 * Y / T + C * (Y / Y ^ (1 / 128 : ℝ))) ≤ _
    calc
      _ ≤ (8 / 3 : ℝ) * Y * (2 * G) ^ 2 * (20 * G) ^ 2 *
          ((2 + C) * Y / G ^ 16) := by gcongr
      _ = (12800 / 3 : ℝ) * (2 + C) * Y ^ 2 / G ^ 12 := by
        field_simp
        ring
      _ ≤ 5000 * (2 + C) * Y ^ 2 / G ^ 12 := by
        have hfac : 0 ≤ (2 + C) * Y ^ 2 / G ^ 12 := by positivity
        calc
          (12800 / 3 : ℝ) * (2 + C) * Y ^ 2 / G ^ 12 =
              (12800 / 3 : ℝ) * ((2 + C) * Y ^ 2 / G ^ 12) := by ring
          _ ≤
              5000 * ((2 + C) * Y ^ 2 / G ^ 12) := by gcongr <;> norm_num
          _ = 5000 * (2 + C) * Y ^ 2 / G ^ 12 := by ring
  have hDsq : D ^ 2 = 5000 * (2 + C) := by
    change reciprocalFourthEnvelopeConstant ^ 2 = _
    unfold reciprocalFourthEnvelopeConstant
    rw [Real.sq_sqrt]
    positivity
  have hsqrtA : Real.sqrt (reciprocalVaughanBlockMajorant
      T y (reciprocalVaughanCutoff y)) ≤ D * Y / G ^ 6 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    calc
      _ ≤ 5000 * (2 + C) * Y ^ 2 / G ^ 12 := hA
      _ = (D * Y / G ^ 6) ^ 2 := by
        rw [div_pow, mul_pow, hDsq]
        ring
  have hcard := card_dyadicExponentRange_le_four_log hy
  change ((dyadicExponentRange y).card : ℝ) ≤ 4 * G at hcard
  have hcard0 : (0 : ℝ) ≤ (dyadicExponentRange y).card := by positivity
  have hcardSq : ((dyadicExponentRange y).card : ℝ) ^ 2 ≤ 16 * G ^ 2 := by
    nlinarith
  change ((dyadicExponentRange y).card : ℝ) ^ 2 *
      Real.sqrt (reciprocalVaughanBlockMajorant T y (reciprocalVaughanCutoff y)) ≤
    16 * D * Y / G ^ 4
  calc
    _ ≤ (16 * G ^ 2) * (D * Y / G ^ 6) := by gcongr
    _ = 16 * D * Y / G ^ 4 := by field_simp

lemma tendsto_reciprocalChebyshev_fourth_envelope :
    Tendsto (fun y : ℕ ↦
      16 * reciprocalFourthEnvelopeConstant /
        (Real.log (y : ℝ)) ^ 4) atTop (nhds 0) := by
  have hlog : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlog4 : Tendsto (fun y : ℕ ↦ (Real.log (y : ℝ)) ^ 4)
      atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : 4 ≠ 0)).comp hlog
  have hinv : Tendsto (fun y : ℕ ↦
      ((Real.log (y : ℝ)) ^ 4)⁻¹) atTop (nhds 0) := by
    exact hlog4.inv_tendsto_atTop
  convert hinv.const_mul (16 * reciprocalFourthEnvelopeConstant) using 1 <;>
    simp [div_eq_mul_inv]

theorem tendsto_reciprocalChebyshevMajorant_div :
    Tendsto (fun y : ℕ ↦
      reciprocalChebyshevMajorant y (reciprocalVaughanCutoff y)
        (reciprocalDifferencingLength y) / (y : ℝ)) atTop (nhds 0) := by
  let F : ℕ → ℝ := fun y ↦
    reciprocalChebyshevMajorant y (reciprocalVaughanCutoff y)
      (reciprocalDifferencingLength y) / (y : ℝ)
  let E : ℕ → ℝ := fun y ↦
    (176 * (Real.log (y : ℝ)) ^ 33 *
      (y : ℝ) ^ (13 / 16 : ℝ)) / (y : ℝ) +
      16 * reciprocalFourthEnvelopeConstant /
        (Real.log (y : ℝ)) ^ 4
  have hE : Tendsto E atTop (nhds 0) := by
    dsimp only [E]
    convert tendsto_reciprocalChebyshev_type_envelope.add
      tendsto_reciprocalChebyshev_fourth_envelope using 1 <;> norm_num
  have hlog := eventually_log_natCast_le_rpow (1 / 8 : ℝ) (by norm_num)
  have hlogpowRaw := eventually_log_natCast_rpow_le_rpow
    (16 : ℝ) (1 / 128 : ℝ) (by norm_num) (by norm_num)
  have hlogpow : ∀ᶠ y : ℕ in atTop,
      (Real.log (y : ℝ)) ^ 16 ≤ (y : ℝ) ^ (1 / 128 : ℝ) := by
    filter_upwards [hlogpowRaw] with y hy
    rw [← Real.rpow_natCast]
    exact hy
  have hnonneg : ∀ᶠ y : ℕ in atTop, 0 ≤ F y := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    have hlog0 : 0 ≤ Real.log (y : ℝ) := Real.log_natCast_nonneg y
    have hT : 0 < reciprocalVaughanCutoff y := reciprocalVaughanCutoff_pos y
    have hA := reciprocalVaughanBlockMajorant_nonneg
      (V := (reciprocalVaughanCutoff y : ℝ)) (y := y) hT
    have hB : 0 ≤ reciprocalTypeIMajorant y
        (reciprocalDifferencingLength y) := reciprocalTypeIMajorant_nonneg
    dsimp only [F]
    unfold reciprocalChebyshevMajorant
    apply div_nonneg
    · apply add_nonneg
      · apply add_nonneg <;> positivity
      · positivity
    · positivity
  have hbound : ∀ᶠ y : ℕ in atTop, F y ≤ E y := by
    filter_upwards [eventually_ge_atTop 4, hlog, hlogpow] with y hy hylog hylogpow
    let Y : ℝ := y
    have hYpos : 0 < Y := by positivity
    have htype := reciprocalChebyshev_type_terms_le hy hylog
    have hfourth := reciprocalChebyshev_fourth_term_le hy hylogpow
    dsimp only [F, E]
    unfold reciprocalChebyshevMajorant
    have hsum := add_le_add htype hfourth
    calc
      _ ≤ (176 * Real.log (y : ℝ) ^ 33 * (y : ℝ) ^ (13 / 16 : ℝ) +
          16 * reciprocalFourthEnvelopeConstant * (y : ℝ) /
            Real.log (y : ℝ) ^ 4) / (y : ℝ) :=
        div_le_div_of_nonneg_right hsum hYpos.le
      _ = (176 * Real.log (y : ℝ) ^ 33 * (y : ℝ) ^ (13 / 16 : ℝ)) /
          (y : ℝ) + 16 * reciprocalFourthEnvelopeConstant /
            Real.log (y : ℝ) ^ 4 := by field_simp
  exact squeeze_zero' hnonneg hbound hE

lemma eventually_reciprocal_parameters_size :
    ∀ᶠ y : ℕ in atTop,
      16 * reciprocalDifferencingLength y *
          ((reciprocalVaughanCutoff y) ^ 2) ^ 2 ≤ y / 2 := by
  have hlogpowRaw := eventually_log_natCast_rpow_le_rpow
    (64 : ℝ) (1 / 8 : ℝ) (by norm_num) (by norm_num)
  have hgrowth : Tendsto (fun y : ℕ ↦ (y : ℝ) ^ (3 / 8 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 8)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge : ∀ᶠ y : ℕ in atTop,
      (1024 : ℝ) ≤ (y : ℝ) ^ (3 / 8 : ℝ) :=
    hgrowth (eventually_ge_atTop 1024)
  filter_upwards [eventually_ge_atTop 4, hlogpowRaw, hlarge] with y hy hylog hlargeY
  let Y : ℝ := y
  let G : ℝ := Real.log Y
  let T : ℝ := reciprocalVaughanCutoff y
  let L : ℝ := reciprocalDifferencingLength y
  have hYpos : 0 < Y := by positivity
  have hG0 : 0 ≤ G := Real.log_natCast_nonneg y
  have hT : T ≤ 2 * G ^ 16 := by
    simpa only [T, G, Y] using reciprocalVaughanCutoff_le_two_log_pow hy
  have hL : L ≤ 2 * Real.sqrt Y := by
    simpa only [L, Y] using
      reciprocalDifferencingLength_le_two_sqrt (show 1 ≤ y by omega)
  have hTpow : T ^ 4 ≤ 16 * G ^ 64 := by
    calc
      _ ≤ (2 * G ^ 16) ^ 4 := by gcongr
      _ = 16 * G ^ 64 := by ring
  have hylog' : G ^ 64 ≤ Y ^ (1 / 8 : ℝ) := by
    calc
      G ^ 64 = G ^ (64 : ℝ) := (Real.rpow_natCast G 64).symm
      _ ≤ Y ^ (1 / 8 : ℝ) := by simpa only [G, Y] using hylog
  have hsqrt : Real.sqrt Y = Y ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow Y
  have hexp : Real.sqrt Y * Y ^ (1 / 8 : ℝ) = Y ^ (5 / 8 : ℝ) := by
    rw [hsqrt, ← Real.rpow_add hYpos]
    norm_num
  have hscale : (1024 : ℝ) * Y ^ (5 / 8 : ℝ) ≤ Y := by
    calc
      _ ≤ Y ^ (3 / 8 : ℝ) * Y ^ (5 / 8 : ℝ) := by gcongr
      _ = Y := by
        rw [← Real.rpow_add hYpos]
        norm_num
  have hreal : ((2 * (16 * reciprocalDifferencingLength y *
      ((reciprocalVaughanCutoff y) ^ 2) ^ 2) : ℕ) : ℝ) ≤ (y : ℝ) := by
    push_cast
    change 2 * (16 * L * (T ^ 2) ^ 2) ≤ Y
    calc
      _ = 32 * L * T ^ 4 := by ring
      _ ≤ 32 * (2 * Real.sqrt Y) * (16 * G ^ 64) := by gcongr
      _ = 1024 * Real.sqrt Y * G ^ 64 := by ring
      _ ≤ 1024 * Real.sqrt Y * Y ^ (1 / 8 : ℝ) := by gcongr
      _ = 1024 * (Real.sqrt Y * Y ^ (1 / 8 : ℝ)) := by ring
      _ = 1024 * Y ^ (5 / 8 : ℝ) := by rw [hexp]
      _ ≤ Y := hscale
  have hnat : 2 * (16 * reciprocalDifferencingLength y *
      ((reciprocalVaughanCutoff y) ^ 2) ^ 2) ≤ y := by exact_mod_cast hreal
  omega

end

end ReciprocalChebyshevAsymptotic
end Erdos378
