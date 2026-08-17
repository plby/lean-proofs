/- leanprover/lean4:v4.33.0 -/

import ErdosProblems.Erdos175.VaughanTypeIICoefficients

/-!
# Closed coefficient bounds for the Vaughan Type-II blocks

This file is deliberately independent of the proof of the analytic
near--far estimate.  It turns a bound for `dyadicAnalyticFactor` on an
active oriented rectangle into a closed `y^(27/28)` bound for each of the
two coefficient majorants.
-/

noncomputable section

namespace Erdos175.TypeIICoefficientCollapse

open Erdos175.VaughanTypeIIDyadic
open Erdos175.VaughanTypeIICoefficients

private lemma rpow_half_mul_rpow_thirteen_twentyEight
    {y : ℝ} (hy : 0 < y) :
    y ^ (1 / 2 : ℝ) * y ^ (13 / 28 : ℝ) = y ^ (27 / 28 : ℝ) := by
  rw [← Real.rpow_add hy]
  norm_num

private lemma one_le_pow_four {H : ℝ} (hH : 1 ≤ H) : 1 ≤ H ^ 4 := by
  nlinarith [sq_nonneg (H ^ 2 - 1),
    mul_nonneg (sub_nonneg.mpr hH) (by linarith : 0 ≤ H + 1)]

private lemma pow_two_le_pow_six {H : ℝ} (hH : 1 ≤ H) : H ^ 2 ≤ H ^ 6 := by
  have hH4 : 1 ≤ H ^ 4 := one_le_pow_four hH
  calc
    H ^ 2 = H ^ 2 * 1 := by ring
    _ ≤ H ^ 2 * H ^ 4 := mul_le_mul_of_nonneg_left hH4 (sq_nonneg H)
    _ = H ^ 6 := by ring

private lemma pow_five_le_pow_six {H : ℝ} (hH : 1 ≤ H) : H ^ 5 ≤ H ^ 6 := by
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  calc
    H ^ 5 = H ^ 5 * 1 := by ring
    _ ≤ H ^ 5 * H := mul_le_mul_of_nonneg_left hH (by positivity)
    _ = H ^ 6 := by ring

/-! The next two lemmas contain all coefficient-specific algebra. -/

/-- A constant block paired with a logarithmically weighted block costs at
most `2 sqrt(y) H³` when the product of their dyadic scales is at most
`2y`.  The third power of `H` is intentionally generous, so that both
Type-II coefficient families share one final log exponent. -/
lemma sqrt_const_mul_sqrt_logMass_le
    {y A B : ℕ} {H : ℝ}
    (hy : 0 < y) (hA : 0 < A) (hB : 0 < B)
    (hAB : A * B ≤ 2 * y) (hH : 1 ≤ H)
    (hlog : Real.log (2 * (A : ℝ)) ≤ H) :
    Real.sqrt B *
        Real.sqrt ((A : ℝ) * Real.log (2 * (A : ℝ)) ^ 2) ≤
      2 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3 := by
  let ell := Real.log (2 * (A : ℝ))
  let c := Real.sqrt B * Real.sqrt ((A : ℝ) * ell ^ 2)
  have hell0 : 0 ≤ ell := by
    dsimp only [ell]
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast (show 1 ≤ 2 * A by omega)
    exact this
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have hellsq : ell ^ 2 ≤ H ^ 2 := by
    have hell : ell ≤ H := by simpa only [ell] using hlog
    nlinarith
  have hABR : (A : ℝ) * B ≤ 2 * (y : ℝ) := by
    exact_mod_cast hAB
  have hmass0 : 0 ≤ (A : ℝ) * ell ^ 2 := by positivity
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hcsq : c ^ 2 = ((A : ℝ) * B) * ell ^ 2 := by
    dsimp only [c]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (B : ℝ)),
      Real.sq_sqrt hmass0]
    ring
  have hcsq_le : c ^ 2 ≤ 2 * (y : ℝ) * H ^ 2 := by
    rw [hcsq]
    gcongr
  have hyr0 : 0 ≤ (y : ℝ) := by positivity
  have hyrpow : ((y : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (y : ℝ) := by
    rw [← Real.rpow_mul_natCast hyr0]
    norm_num [Real.rpow_one]
  have htargetsq :
      c ^ 2 ≤ (2 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) ^ 2 := by
    have htarget :
        (2 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) ^ 2 =
          4 * (y : ℝ) * H ^ 6 := by
      rw [mul_pow, mul_pow, hyrpow]
      ring
    rw [htarget]
    calc
      c ^ 2 ≤ 2 * (y : ℝ) * H ^ 2 := hcsq_le
      _ ≤ 4 * (y : ℝ) * H ^ 6 := by gcongr <;> norm_num
  change c ≤ _
  have ht0 : 0 ≤ 2 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3 := by positivity
  nlinarith

/-- The shifted Möbius-convolution mass paired with a von Mangoldt mass
costs at most `4 sqrt(y) H³`.  Here `A` is the scale carrying the shifted
coefficient and `B` the scale carrying von Mangoldt. -/
lemma sqrt_lambdaMass_mul_sqrt_aMass_le
    {y M A B : ℕ} {H : ℝ}
    (hy : 0 < y) (hM : 1 ≤ M) (hA : 0 < A) (hB : 0 < B)
    (hAB : A * B ≤ 2 * y) (hH : 1 ≤ H)
    (hlogScale : Real.log (2 * (B : ℝ)) ≤ H)
    (hlogM : Real.log M + 3 ≤ H) :
    Real.sqrt ((B : ℝ) * Real.log (2 * (B : ℝ)) ^ 2) *
        Real.sqrt ((8 / 9 : ℝ) * (A : ℝ) *
          (Real.log M + 3) ^ 3 + 1) ≤
      4 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3 := by
  let ell := Real.log (2 * (B : ℝ))
  let mu := Real.log M + 3
  let lambdaMass : ℝ := B * ell ^ 2
  let aMass : ℝ := (8 / 9 : ℝ) * A * mu ^ 3 + 1
  let c := Real.sqrt lambdaMass * Real.sqrt aMass
  have hell0 : 0 ≤ ell := by
    dsimp only [ell]
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ 2 * (B : ℝ) := by exact_mod_cast (show 1 ≤ 2 * B by omega)
    exact this
  have hmu0 : 0 ≤ mu := by
    dsimp only [mu]
    have hlogM0 : 0 ≤ Real.log (M : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast hM
    linarith
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have hellsq : ell ^ 2 ≤ H ^ 2 := by
    have hell : ell ≤ H := by simpa only [ell] using hlogScale
    nlinarith
  have hmu3 : mu ^ 3 ≤ H ^ 3 := by
    have hmule : mu ≤ H := by simpa only [mu] using hlogM
    exact pow_le_pow_left₀ hmu0 hmule 3
  have hABR : (A : ℝ) * B ≤ 2 * (y : ℝ) := by exact_mod_cast hAB
  have hBle : (B : ℝ) ≤ 2 * (y : ℝ) := by
    have hAle : (1 : ℝ) ≤ A := by exact_mod_cast hA
    nlinarith [mul_nonneg (sub_nonneg.mpr hAle) (by positivity : 0 ≤ (B : ℝ))]
  have hlambda0 : 0 ≤ lambdaMass := by dsimp only [lambdaMass]; positivity
  have ha0 : 0 ≤ aMass := by dsimp only [aMass]; positivity
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hcsq : c ^ 2 = lambdaMass * aMass := by
    dsimp only [c]
    rw [mul_pow, Real.sq_sqrt hlambda0, Real.sq_sqrt ha0]
  have hinner : (B : ℝ) * ((8 / 9 : ℝ) * A * mu ^ 3 + 1) ≤
      4 * (y : ℝ) * H ^ 3 := by
    calc
      (B : ℝ) * ((8 / 9 : ℝ) * A * mu ^ 3 + 1) =
          (8 / 9 : ℝ) * ((A : ℝ) * B) * mu ^ 3 + B := by ring
      _ ≤ (8 / 9 : ℝ) * (2 * (y : ℝ)) * H ^ 3 +
          2 * (y : ℝ) := by gcongr
      _ ≤ 4 * (y : ℝ) * H ^ 3 := by
        have hH3 : 1 ≤ H ^ 3 :=
          by simpa using
            (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hH 3)
        have hyH : (y : ℝ) ≤ (y : ℝ) * H ^ 3 := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hH3 (by positivity : (0 : ℝ) ≤ y)
        nlinarith [mul_nonneg (by positivity : 0 ≤ (y : ℝ))
          (by positivity : 0 ≤ H ^ 3)]
  have hcsq_le : c ^ 2 ≤ 4 * (y : ℝ) * H ^ 5 := by
    rw [hcsq]
    dsimp only [lambdaMass, aMass]
    calc
      (B : ℝ) * ell ^ 2 *
          ((8 / 9 : ℝ) * (A : ℝ) * mu ^ 3 + 1) =
          ell ^ 2 * ((B : ℝ) *
            ((8 / 9 : ℝ) * A * mu ^ 3 + 1)) := by ring
      _ ≤ H ^ 2 * (4 * (y : ℝ) * H ^ 3) := by gcongr
      _ = 4 * (y : ℝ) * H ^ 5 := by ring
  have hyr0 : 0 ≤ (y : ℝ) := by positivity
  have hyrpow : ((y : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (y : ℝ) := by
    rw [← Real.rpow_mul_natCast hyr0]
    norm_num [Real.rpow_one]
  have htargetsq :
      c ^ 2 ≤ (4 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) ^ 2 := by
    have htarget :
        (4 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) ^ 2 =
          16 * (y : ℝ) * H ^ 6 := by
      rw [mul_pow, mul_pow, hyrpow]
      ring
    rw [htarget]
    calc
      c ^ 2 ≤ 4 * (y : ℝ) * H ^ 5 := hcsq_le
      _ ≤ 16 * (y : ℝ) * H ^ 6 := by gcongr <;> norm_num
  change c ≤ _
  have ht0 : 0 ≤ 4 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3 := by positivity
  nlinarith

/-! ### Block-majorant endpoints -/

/-- Coefficient collapse for an active `Σ₂,₂` block. -/
theorem sigma22OrientedBlockMajorant_le_closed
    {x : ℝ} {y y' j k : ℕ} {C H : ℝ}
    (hy : 0 < y) (hy' : y' ≤ 2 * y)
    (hactive : blockActive y y' j k)
    (_hsupport : sigma22SupportActive 1 j)
    (_hC : 0 ≤ C) (hH : 1 ≤ H)
    (hlogLarge : Real.log (2 * (orientedLargeScale j k : ℝ)) ≤ H)
    (hlogSmall : Real.log (2 * (orientedSmallScale j k : ℝ)) ≤ H)
    (hanalytic :
      (if j < k then dyadicAnalyticFactor x y y' k j 0
       else dyadicAnalyticFactor x y y' j k 0) ≤
        C * (y : ℝ) ^ (13 / 28 : ℝ) * H) :
    sigma22OrientedBlockMajorant x y y' j k 0 ≤
      (2 * C) * (y : ℝ) ^ (27 / 28 : ℝ) * H ^ 4 := by
  have hprod : 2 ^ j * 2 ^ k ≤ 2 * y :=
    (blockActive_lower_product_le hactive).trans hy'
  have hf0 : 0 ≤
      (if j < k then dyadicAnalyticFactor x y y' k j 0
       else dyadicAnalyticFactor x y y' j k 0) := by
    split <;> unfold dyadicAnalyticFactor <;> positivity
  have hyr : 0 < (y : ℝ) := by exact_mod_cast hy
  by_cases hjk : j < k
  · have hcoeff := sqrt_const_mul_sqrt_logMass_le
      hy (pow_pos (by omega) j) (pow_pos (by omega) k) hprod hH (by
        simpa [orientedSmallScale, hjk] using hlogSmall)
    simp only [sigma22OrientedBlockMajorant, hjk, if_pos]
    have hf := hanalytic
    simp only [hjk, if_pos] at hf hf0
    calc
      Real.sqrt (2 ^ k : ℕ) * dyadicAnalyticFactor x y y' k j 0 *
          Real.sqrt ((2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2) =
          (Real.sqrt (2 ^ k : ℕ) *
            Real.sqrt ((2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2)) *
              dyadicAnalyticFactor x y y' k j 0 := by ring
      _ ≤ (2 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) *
          (C * (y : ℝ) ^ (13 / 28 : ℝ) * H) :=
        mul_le_mul hcoeff hf hf0 (by positivity)
      _ = (2 * C) * (y : ℝ) ^ (27 / 28 : ℝ) * H ^ 4 := by
        rw [← rpow_half_mul_rpow_thirteen_twentyEight hyr]
        ring
  · have hcoeff := sqrt_const_mul_sqrt_logMass_le
      hy (pow_pos (by omega) j) (pow_pos (by omega) k) hprod hH (by
        simpa [orientedLargeScale, hjk] using hlogLarge)
    simp only [sigma22OrientedBlockMajorant, hjk, if_neg]
    have hf := hanalytic
    simp only [hjk, if_neg] at hf hf0
    calc
      Real.sqrt ((2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2) *
          dyadicAnalyticFactor x y y' j k 0 * Real.sqrt (2 ^ k : ℕ) =
          (Real.sqrt (2 ^ k : ℕ) *
            Real.sqrt ((2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2)) *
              dyadicAnalyticFactor x y y' j k 0 := by ring
      _ ≤ (2 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) *
          (C * (y : ℝ) ^ (13 / 28 : ℝ) * H) :=
        mul_le_mul hcoeff hf hf0 (by positivity)
      _ = (2 * C) * (y : ℝ) ^ (27 / 28 : ℝ) * H ^ 4 := by
        rw [← rpow_half_mul_rpow_thirteen_twentyEight hyr]
        ring

/-- Coefficient collapse for an active `Σ₃` block. -/
theorem sigma3OrientedBlockMajorant_le_closed
    {x : ℝ} {y y' M j k : ℕ} {C H : ℝ}
    (hy : 0 < y) (hy' : y' ≤ 2 * y) (hM : 1 ≤ M)
    (hactive : blockActive y y' j k)
    (_hsupport : sigma3SupportActive M M j k)
    (_hC : 0 ≤ C) (hH : 1 ≤ H)
    (hlogLarge : Real.log (2 * (orientedLargeScale j k : ℝ)) ≤ H)
    (hlogSmall : Real.log (2 * (orientedSmallScale j k : ℝ)) ≤ H)
    (hlogM : Real.log M + 3 ≤ H)
    (hanalytic :
      (if j < k then dyadicAnalyticFactor x y y' k j 0
       else dyadicAnalyticFactor x y y' j k 0) ≤
        C * (y : ℝ) ^ (13 / 28 : ℝ) * H) :
    sigma3OrientedBlockMajorant x y y' M j k 0 ≤
      (4 * C) * (y : ℝ) ^ (27 / 28 : ℝ) * H ^ 4 := by
  have hprod : 2 ^ j * 2 ^ k ≤ 2 * y :=
    (blockActive_lower_product_le hactive).trans hy'
  have hf0 : 0 ≤
      (if j < k then dyadicAnalyticFactor x y y' k j 0
       else dyadicAnalyticFactor x y y' j k 0) := by
    split <;> unfold dyadicAnalyticFactor <;> positivity
  have hyr : 0 < (y : ℝ) := by exact_mod_cast hy
  by_cases hjk : j < k
  · have hcoeff := sqrt_lambdaMass_mul_sqrt_aMass_le
      hy hM (pow_pos (by omega) j) (pow_pos (by omega) k) hprod hH (by
        simpa [orientedLargeScale, hjk] using hlogLarge) hlogM
    simp only [sigma3OrientedBlockMajorant, hjk, if_pos]
    have hf := hanalytic
    simp only [hjk, if_pos] at hf hf0
    calc
      Real.sqrt ((2 ^ k : ℕ) * Real.log (2 * (2 ^ k : ℕ)) ^ 2) *
          dyadicAnalyticFactor x y y' k j 0 *
            Real.sqrt ((8 / 9 : ℝ) * (2 ^ j : ℕ) * (Real.log M + 3) ^ 3 + 1) =
          (Real.sqrt ((2 ^ k : ℕ) * Real.log (2 * (2 ^ k : ℕ)) ^ 2) *
            Real.sqrt ((8 / 9 : ℝ) * (2 ^ j : ℕ) *
              (Real.log M + 3) ^ 3 + 1)) *
                dyadicAnalyticFactor x y y' k j 0 := by ring
      _ ≤ (4 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) *
          (C * (y : ℝ) ^ (13 / 28 : ℝ) * H) :=
        mul_le_mul hcoeff hf hf0 (by positivity)
      _ = (4 * C) * (y : ℝ) ^ (27 / 28 : ℝ) * H ^ 4 := by
        rw [← rpow_half_mul_rpow_thirteen_twentyEight hyr]
        ring
  · have hcoeff := sqrt_lambdaMass_mul_sqrt_aMass_le
      hy hM (pow_pos (by omega) j) (pow_pos (by omega) k) hprod hH (by
        simpa [orientedSmallScale, hjk] using hlogSmall) hlogM
    simp only [sigma3OrientedBlockMajorant, hjk, if_neg]
    have hf := hanalytic
    simp only [hjk, if_neg] at hf hf0
    calc
      Real.sqrt ((8 / 9 : ℝ) * (2 ^ j : ℕ) * (Real.log M + 3) ^ 3 + 1) *
          dyadicAnalyticFactor x y y' j k 0 *
            Real.sqrt ((2 ^ k : ℕ) * Real.log (2 * (2 ^ k : ℕ)) ^ 2) =
          (Real.sqrt ((2 ^ k : ℕ) * Real.log (2 * (2 ^ k : ℕ)) ^ 2) *
            Real.sqrt ((8 / 9 : ℝ) * (2 ^ j : ℕ) *
              (Real.log M + 3) ^ 3 + 1)) *
                dyadicAnalyticFactor x y y' j k 0 := by ring
      _ ≤ (4 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) *
          (C * (y : ℝ) ^ (13 / 28 : ℝ) * H) :=
        mul_le_mul hcoeff hf hf0 (by positivity)
      _ = (4 * C) * (y : ℝ) ^ (27 / 28 : ℝ) * H ^ 4 := by
        rw [← rpow_half_mul_rpow_thirteen_twentyEight hyr]
        ring

#print axioms sigma22OrientedBlockMajorant_le_closed
#print axioms sigma3OrientedBlockMajorant_le_closed

end Erdos175.TypeIICoefficientCollapse
