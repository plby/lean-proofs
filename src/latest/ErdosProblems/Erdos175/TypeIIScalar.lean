/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos175.TypeIINearFar

/-!
# Scalar simplification of the Type-II power-block bound

This file turns the three-branch closed correlation majorant into a single
power-saving estimate.  The hypotheses are precisely the scale information
available for an oriented active Vaughan block.  The lower frequency bound
`y^2 ≤ x` is essential: the direct summand of `orientedPowerBlockFarQ`
contains `1 / x`.
-/

noncomputable section

namespace Erdos175.TypeIIScalar

/-- The logarithmic envelope used for all three branches. -/
noncomputable def scalarLog (y : ℕ) : ℝ :=
  Real.log (256 * (y : ℝ) ^ 2)

lemma scalarLog_one_le {y : ℕ} (hy : 1 ≤ y) :
    1 ≤ scalarLog y := by
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have harg : (256 : ℝ) ≤ 256 * (y : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((y : ℝ) - 1)]
  have hlog256 : (1 : ℝ) ≤ Real.log 256 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    have hlog2 := Real.log_two_gt_d9
    norm_num at hlog2 ⊢
    nlinarith
  exact hlog256.trans (Real.log_le_log (by norm_num) harg)

/-- On an oriented block, the local logarithm is swallowed by twice the
global envelope. -/
lemma one_add_log_two_mul_le_two_scalarLog
    {y U V : ℕ} (hy : 1 ≤ y) (hU : 0 < U) (hV : 0 < V)
    (hproduct : U * V ≤ 2 * y) :
    1 + Real.log (2 * (U : ℝ)) ≤ 2 * scalarLog y := by
  have hUle : U ≤ 2 * y := by
    have hVU : U ≤ U * V := by
      calc U = U * 1 := by omega
        _ ≤ U * V := Nat.mul_le_mul_left U hV
    exact hVU.trans hproduct
  have harg : (2 : ℝ) * U ≤ 256 * (y : ℝ) ^ 2 := by
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
    have hUR : (U : ℝ) ≤ 2 * y := by exact_mod_cast hUle
    nlinarith [sq_nonneg ((y : ℝ) - 1)]
  have hlog : Real.log (2 * (U : ℝ)) ≤ scalarLog y := by
    unfold scalarLog
    apply Real.log_le_log
    · positivity
    · exact harg
  have hH := scalarLog_one_le hy
  linarith

/-- The support-scale cubic estimate gives the convenient real upper bound
`U ≤ 8 y^(2/3)`. -/
lemma upperScale_le_eight_rpow
    {y U : ℕ} (hy : 1 ≤ y) (hUcube : U ^ 3 ≤ 512 * y ^ 2) :
    (U : ℝ) ≤ 8 * (y : ℝ) ^ (2 / 3 : ℝ) := by
  have hy0 : 0 ≤ (y : ℝ) := by positivity
  have hpow : ((y : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (y : ℝ) ^ 2 := by
    rw [← Real.rpow_mul_natCast hy0]
    norm_num [Real.rpow_natCast]
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
  rw [mul_pow, hpow]
  norm_num
  exact_mod_cast hUcube

/-- The direct branch after multiplication by the second block length. -/
lemma directTerm_mul_smallScale_le
    {x : ℝ} {y U V : ℕ} (hy : 1 ≤ y) (hV : 0 < V)
    (hVU : V ≤ U) (hproduct : U * V ≤ 2 * y)
    (hxlower : (y : ℝ) ^ 2 ≤ x) :
    (16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 / x) * V ≤
      128 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hx : 0 < x := lt_of_lt_of_le (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hyR)) hxlower
  have hP : (U : ℝ) * V ≤ 2 * (y : ℝ) := by exact_mod_cast hproduct
  have hv2 : (V : ℝ) ^ 2 ≤ 2 * (y : ℝ) := by
    have hVU' : (V : ℝ) ≤ U := by exact_mod_cast hVU
    calc
      (V : ℝ) ^ 2 ≤ (U : ℝ) * V := by nlinarith
      _ ≤ 2 * (y : ℝ) := hP
  have hvroot : (V : ℝ) ≤ 2 * (y : ℝ) ^ (1 / 2 : ℝ) := by
    have hy0 : 0 ≤ (y : ℝ) := by positivity
    have hp : ((y : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (y : ℝ) := by
      rw [← Real.rpow_mul_natCast hy0]
      norm_num [Real.rpow_natCast]
    apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity)
    rw [mul_pow, hp]
    nlinarith
  have hdirect :
      (16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 / x) * V ≤ 64 * V := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hx]
    have hPsq : ((U : ℝ) * V) ^ 2 ≤ (2 * (y : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hP 2
    have hmul := mul_le_mul_of_nonneg_left hxlower (by positivity : (0 : ℝ) ≤ 64 * V)
    nlinarith [hPsq]
  have hexp : (y : ℝ) ^ (1 / 2 : ℝ) ≤
      (y : ℝ) ^ (13 / 14 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hyR (by norm_num)
  have hH := scalarLog_one_le hy
  have hHsq : 1 ≤ scalarLog y ^ 2 := by nlinarith
  calc
    (16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 / x) * V ≤ 64 * V := hdirect
    _ ≤ 64 * (2 * (y : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hvroot (by norm_num)
    _ = 128 * (y : ℝ) ^ (1 / 2 : ℝ) := by ring
    _ ≤ 128 * (y : ℝ) ^ (13 / 14 : ℝ) := by gcongr
    _ ≤ 128 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
      exact le_mul_of_one_le_right (by positivity) hHsq

/-- A scale-free twelfth-power estimate for the sixth-root expression in
the two-step branch. -/
lemma sixthRoot_ratio_mul_rpow_le_three
    {x : ℝ} {y U V : ℕ} (hy : 1 ≤ y) (hU : 0 < U) (hV : 0 < V)
    (hVU : V ≤ U) (hactive : y < 4 * (U * V))
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) (hx : 0 ≤ x) :
    (x / ((V : ℝ) * (U : ℝ) ^ 4)) ^ (1 / 6 : ℝ) *
        (y : ℝ) ^ (1 / 12 : ℝ) ≤ 3 := by
  let r : ℝ := x / ((V : ℝ) * (U : ℝ) ^ 4)
  have hy0 : 0 ≤ (y : ℝ) := by positivity
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hactiveR : (y : ℝ) ≤ 4 * ((U : ℝ) * V) := by
    have h : y ≤ 4 * (U * V) := hactive.le
    exact_mod_cast h
  have hx2 : x ^ 2 ≤ 144 * (y : ℝ) ^ 4 := by
    have := pow_le_pow_left₀ hx hxupper 2
    nlinarith
  have hy5 : (y : ℝ) ^ 5 ≤ 4 ^ 5 * (((U : ℝ) * V) ^ 5) := by
    have := pow_le_pow_left₀ hy0 hactiveR 5
    calc
      (y : ℝ) ^ 5 ≤ (4 * ((U : ℝ) * V)) ^ 5 := this
      _ = 4 ^ 5 * (((U : ℝ) * V) ^ 5) := by ring
  have hv3 : (V : ℝ) ^ 3 ≤ (U : ℝ) ^ 3 := by
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hVU) 3
  have hpoly : r ^ 2 * (y : ℝ) ≤ 147456 := by
    have hden : 0 < (((V : ℝ) * (U : ℝ) ^ 4) ^ 2) := by positivity
    dsimp only [r]
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ hden]
    calc
      x ^ 2 * (y : ℝ) ≤ (144 * (y : ℝ) ^ 4) * (y : ℝ) := by gcongr
      _ = 144 * (y : ℝ) ^ 5 := by ring
      _ ≤ 144 * (4 ^ 5 * (((U : ℝ) * V) ^ 5)) := by gcongr
      _ ≤ 147456 * (((V : ℝ) * (U : ℝ) ^ 4) ^ 2) := by
        have hcomp : (((U : ℝ) * V) ^ 5) ≤
            ((V : ℝ) * (U : ℝ) ^ 4) ^ 2 := by
          calc
            ((U : ℝ) * V) ^ 5 =
                (U : ℝ) ^ 5 * (V : ℝ) ^ 2 * (V : ℝ) ^ 3 := by ring
            _ ≤ (U : ℝ) ^ 5 * (V : ℝ) ^ 2 * (U : ℝ) ^ 3 := by gcongr
            _ = ((V : ℝ) * (U : ℝ) ^ 4) ^ 2 := by ring
        calc
          144 * (4 ^ 5 * (((U : ℝ) * V) ^ 5)) =
              147456 * (((U : ℝ) * V) ^ 5) := by ring_nf
          _ ≤ 147456 * (((V : ℝ) * (U : ℝ) ^ 4) ^ 2) :=
            mul_le_mul_of_nonneg_left hcomp (by norm_num)
  have hpow :
      (r ^ (1 / 6 : ℝ) * (y : ℝ) ^ (1 / 12 : ℝ)) ^ 12 =
        r ^ 2 * (y : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hr0,
      ← Real.rpow_mul_natCast hy0]
    norm_num [Real.rpow_natCast]
  apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by positivity)
  rw [hpow]
  norm_num
  exact hpoly.trans (by norm_num)

/-- The two-step sixth-root branch after multiplication by the small block
length. -/
lemma sixthRootTerm_mul_smallScale_le
    {x : ℝ} {y U V : ℕ} (hy : 1 ≤ y) (hU : 0 < U) (hV : 0 < V)
    (hVU : V ≤ U) (hactive : y < 4 * (U * V))
    (hproduct : U * V ≤ 2 * y)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) (hx : 0 ≤ x) :
    (128 * (U : ℝ) *
      (x / ((V : ℝ) * (U : ℝ) ^ 4)) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log (2 * (U : ℝ)))) * V ≤
      1536 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
  let r : ℝ := x / ((V : ℝ) * (U : ℝ) ^ 4)
  let L : ℝ := 1 + Real.log (2 * (U : ℝ))
  let H : ℝ := scalarLog y
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hyp : 0 < (y : ℝ) := lt_of_lt_of_le zero_lt_one hyR
  have hy12pos : 0 < (y : ℝ) ^ (1 / 12 : ℝ) :=
    Real.rpow_pos_of_pos hyp _
  have hratio := sixthRoot_ratio_mul_rpow_le_three
    hy hU hV hVU hactive hxupper hx
  have hP : (U : ℝ) * V ≤ 2 * (y : ℝ) := by exact_mod_cast hproduct
  have hLone : 1 ≤ L := by
    dsimp only [L]
    have : 0 ≤ Real.log (2 * (U : ℝ)) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ 2 * U := by exact_mod_cast (show 1 ≤ 2 * U by omega)
      exact this
    linarith
  have hLH : L ≤ 2 * H := by
    simpa only [L, H] using
      one_add_log_two_mul_le_two_scalarLog hy hU hV hproduct
  have hsqrt : Real.sqrt L ≤ 2 * H := by
    calc
      Real.sqrt L ≤ L := Real.sqrt_le_self_iff.mpr (Or.inr hLone)
      _ ≤ 2 * H := hLH
  have hscaled :
      (128 * (U : ℝ) * r ^ (1 / 6 : ℝ) * Real.sqrt L * V) *
          (y : ℝ) ^ (1 / 12 : ℝ) ≤ 1536 * (y : ℝ) * H := by
    calc
      (128 * (U : ℝ) * r ^ (1 / 6 : ℝ) * Real.sqrt L * V) *
          (y : ℝ) ^ (1 / 12 : ℝ) =
          128 * ((U : ℝ) * V) *
            (r ^ (1 / 6 : ℝ) * (y : ℝ) ^ (1 / 12 : ℝ)) *
              Real.sqrt L := by ring
      _ ≤ 128 * (2 * (y : ℝ)) * 3 * (2 * H) := by gcongr
      _ = 1536 * (y : ℝ) * H := by ring
  have hroot :
      128 * (U : ℝ) * r ^ (1 / 6 : ℝ) * Real.sqrt L * V ≤
        1536 * (y : ℝ) ^ (11 / 12 : ℝ) * H := by
    apply le_of_mul_le_mul_right
    · calc
      (128 * (U : ℝ) * r ^ (1 / 6 : ℝ) * Real.sqrt L * V) *
          (y : ℝ) ^ (1 / 12 : ℝ) ≤ 1536 * (y : ℝ) * H := hscaled
      _ = (1536 * (y : ℝ) ^ (11 / 12 : ℝ) * H) *
          (y : ℝ) ^ (1 / 12 : ℝ) := by
        have hyadd :
            (y : ℝ) ^ (11 / 12 : ℝ) * (y : ℝ) ^ (1 / 12 : ℝ) =
              (y : ℝ) := by
          rw [← Real.rpow_add hyp]
          norm_num
        calc
          1536 * (y : ℝ) * H =
              1536 * ((y : ℝ) ^ (11 / 12 : ℝ) *
                (y : ℝ) ^ (1 / 12 : ℝ)) * H := by rw [hyadd]
          _ = (1536 * (y : ℝ) ^ (11 / 12 : ℝ) * H) *
              (y : ℝ) ^ (1 / 12 : ℝ) := by ring
    · exact hy12pos
  have hexp : (y : ℝ) ^ (11 / 12 : ℝ) ≤
      (y : ℝ) ^ (13 / 14 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hyR (by norm_num)
  have hH : 1 ≤ H := by simpa only [H] using scalarLog_one_le hy
  dsimp only [r, L, H] at hroot ⊢
  calc
    128 * (U : ℝ) *
        (x / ((V : ℝ) * (U : ℝ) ^ 4)) ^ (1 / 6 : ℝ) *
          Real.sqrt (1 + Real.log (2 * (U : ℝ))) * V ≤
        1536 * (y : ℝ) ^ (11 / 12 : ℝ) * scalarLog y := hroot
    _ ≤ 1536 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y := by gcongr
    _ ≤ 1536 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
      gcongr
      nlinarith

/-- The fractional-power factor in the interpolated branch. -/
lemma upperSixSevenths_mul_smallScale_le
    {y U V : ℕ} (hy : 1 ≤ y) (hV : 0 < V) (hVU : V ≤ U)
    (hproduct : U * V ≤ 2 * y) :
    (2 * (U : ℝ)) ^ (6 / 7 : ℝ) * V ≤
      8 * (y : ℝ) ^ (13 / 14 : ℝ) := by
  have hy0 : 0 ≤ (y : ℝ) := by positivity
  have hu0 : 0 ≤ (U : ℝ) := by positivity
  have htwo : (2 : ℝ) ^ (6 / 7 : ℝ) ≤ 2 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hmul : (2 * (U : ℝ)) ^ (6 / 7 : ℝ) ≤
      2 * (U : ℝ) ^ (6 / 7 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hu0]
    gcongr
  have hP : (U : ℝ) * V ≤ 2 * (y : ℝ) := by exact_mod_cast hproduct
  have hv2 : (V : ℝ) ^ 2 ≤ 2 * (y : ℝ) := by
    have hVU' : (V : ℝ) ≤ U := by exact_mod_cast hVU
    calc
      (V : ℝ) ^ 2 ≤ (U : ℝ) * V := by nlinarith
      _ ≤ 2 * (y : ℝ) := hP
  let D : ℝ := (U : ℝ) ^ (6 / 7 : ℝ) * V
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hDpow : D ^ 14 = (U : ℝ) ^ 12 * (V : ℝ) ^ 14 := by
    dsimp only [D]
    rw [mul_pow, ← Real.rpow_mul_natCast hu0]
    norm_num [Real.rpow_natCast]
  have hyPow : ((y : ℝ) ^ (13 / 14 : ℝ)) ^ 14 = (y : ℝ) ^ 13 := by
    rw [← Real.rpow_mul_natCast hy0]
    norm_num [Real.rpow_natCast]
  have hDbound : D ≤ 4 * (y : ℝ) ^ (13 / 14 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (14 : ℕ) ≠ 0) (by positivity)
    rw [hDpow, mul_pow, hyPow]
    have hPpow : ((U : ℝ) * V) ^ 12 ≤
        (2 * (y : ℝ)) ^ 12 := pow_le_pow_left₀ (by positivity) hP 12
    calc
      (U : ℝ) ^ 12 * (V : ℝ) ^ 14 =
          (((U : ℝ) * V) ^ 12) * (V : ℝ) ^ 2 := by ring
      _ ≤ (2 * (y : ℝ)) ^ 12 * (2 * (y : ℝ)) := by gcongr
      _ ≤ 4 ^ 14 * (y : ℝ) ^ 13 := by
        have : (0 : ℝ) ≤ (y : ℝ) ^ 13 := by positivity
        norm_num
        nlinarith
  calc
    (2 * (U : ℝ)) ^ (6 / 7 : ℝ) * V ≤
        (2 * (U : ℝ) ^ (6 / 7 : ℝ)) * V := by gcongr
    _ = 2 * D := by dsimp only [D]; ring
    _ ≤ 2 * (4 * (y : ℝ) ^ (13 / 14 : ℝ)) :=
      mul_le_mul_of_nonneg_left hDbound (by norm_num)
    _ = 8 * (y : ℝ) ^ (13 / 14 : ℝ) := by ring

/-- The interpolated seventh-root branch after multiplication by the small
block length. -/
lemma seventhRootTerm_mul_smallScale_le
    {y U V : ℕ} (hy : 1 ≤ y) (hV : 0 < V) (hVU : V ≤ U)
    (hproduct : U * V ≤ 2 * y) :
    (128 * (2 * (U : ℝ)) ^ (6 / 7 : ℝ) *
      (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ)) * V ≤
      2048 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
  let L : ℝ := 1 + Real.log (2 * (U : ℝ))
  let H : ℝ := scalarLog y
  have hLone : 1 ≤ L := by
    dsimp only [L]
    have : 0 ≤ Real.log (2 * (U : ℝ)) := by
      apply Real.log_nonneg
      have hU : 0 < U := lt_of_lt_of_le hV (by omega)
      exact_mod_cast (show 1 ≤ 2 * U by omega)
    linarith
  have hLH : L ≤ 2 * H := by
    simpa only [L, H] using
      one_add_log_two_mul_le_two_scalarLog hy (lt_of_lt_of_le hV hVU) hV hproduct
  have hLpow : L ^ (2 / 7 : ℝ) ≤ 2 * H := by
    exact (Real.rpow_le_self_of_one_le hLone (by norm_num)).trans hLH
  have hscale := upperSixSevenths_mul_smallScale_le hy hV hVU hproduct
  have hH : 1 ≤ H := by simpa only [H] using scalarLog_one_le hy
  dsimp only [L, H] at hLpow hH ⊢
  calc
    (128 * (2 * (U : ℝ)) ^ (6 / 7 : ℝ) *
        (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ)) * V =
        128 * ((2 * (U : ℝ)) ^ (6 / 7 : ℝ) * V) *
          (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ) := by ring
    _ ≤ 128 * (8 * (y : ℝ) ^ (13 / 14 : ℝ)) *
          (2 * scalarLog y) := by gcongr
    _ = 2048 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y := by ring
    _ ≤ 2048 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
      gcongr
      nlinarith

/-- The complete scalar estimate used for every oriented active Type-II
power block.  Its exponent `13/28` combines with the coefficient factor
`sqrt (UV)`, of size `y^(1/2)`, to give the final `y^(27/28)` bound. -/
theorem sqrt_two_mul_add_orientedPowerBlockFarQ_mul_le
    {x : ℝ} {y U V : ℕ}
    (hy : 1 ≤ y) (hU : 0 < U) (hV : 0 < V) (hVU : V ≤ U)
    (hactive : y < 4 * (U * V)) (hproduct : U * V ≤ 2 * y)
    (hUcube : U ^ 3 ≤ 512 * y ^ 2)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    Real.sqrt
        (2 * (U : ℝ) +
          TypeII.orientedPowerBlockFarQ x U V * (V : ℝ)) ≤
      64 * (y : ℝ) ^ (13 / 28 : ℝ) * scalarLog y := by
  have hx : 0 < x := by
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
    exact lt_of_lt_of_le (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hyR)) hxlower
  have hbase := upperScale_le_eight_rpow hy hUcube
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hbaseExp : (y : ℝ) ^ (2 / 3 : ℝ) ≤
      (y : ℝ) ^ (13 / 14 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hyR (by norm_num)
  have hH : 1 ≤ scalarLog y := scalarLog_one_le hy
  have hbaseTerm : 2 * (U : ℝ) ≤
      16 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
    calc
      2 * (U : ℝ) ≤ 2 * (8 * (y : ℝ) ^ (2 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ = 16 * (y : ℝ) ^ (2 / 3 : ℝ) := by ring
      _ ≤ 16 * (y : ℝ) ^ (13 / 14 : ℝ) := by gcongr
      _ ≤ 16 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
        exact le_mul_of_one_le_right (by positivity) (by nlinarith [hH])
  have hdirect := directTerm_mul_smallScale_le
    hy hV hVU hproduct hxlower
  have hsixth := sixthRootTerm_mul_smallScale_le
    hy hU hV hVU hactive hproduct hxupper hx.le
  have hseventh := seventhRootTerm_mul_smallScale_le
    hy hV hVU hproduct
  have hinside :
      2 * (U : ℝ) + TypeII.orientedPowerBlockFarQ x U V * (V : ℝ) ≤
        4096 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
    unfold TypeII.orientedPowerBlockFarQ
    nlinarith
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      2 * (U : ℝ) + TypeII.orientedPowerBlockFarQ x U V * (V : ℝ) ≤
          4096 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := hinside
      _ = (64 * (y : ℝ) ^ (13 / 28 : ℝ) * scalarLog y) ^ 2 := by
        have hy0 : 0 ≤ (y : ℝ) := by positivity
        have hp : ((y : ℝ) ^ (13 / 28 : ℝ)) ^ 2 =
            (y : ℝ) ^ (13 / 14 : ℝ) := by
          rw [← Real.rpow_mul_natCast hy0]
          norm_num
        rw [mul_pow, mul_pow, hp]
        norm_num

end Erdos175.TypeIIScalar
