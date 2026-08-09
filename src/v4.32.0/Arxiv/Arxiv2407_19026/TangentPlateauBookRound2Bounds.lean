import Arxiv.Arxiv2407_19026.TangentPlateauBookRound2Certificate

/-!
# Semantic second-round plateau book bound

This file connects the degree-53 exact certificate to the analytic
plateau-book lower bound.
-/

namespace Arxiv2407_19026
namespace PlateauBookRound2Bounds

noncomputable section

open PlateauBookRound2Certificate

def plateauBlueUpperRound2 (z : ℝ) : ℝ :=
  -(35123073 / 125000000) * z ^ 4 +
    1602051239 / 1250000000 * z ^ 3 -
    16753174443 / 10000000000 * z ^ 2 +
    3087130583 / 2500000000 * z +
    49773573 / 10000000000

private lemma plateau_blue_raw_le_round2 {z : ℝ}
    (hz : z ∈ Set.Icc (268 / 1000 : ℝ) (189 / 500)) :
    plateauBlueRawUpper (33 / 1000) z ≤
      plateauBlueUpperRound2 z := by
  let u : ℝ := (1000 * z - 268) / 110
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have h := KernelBounds.bernstein_sum_nonneg 21
    plateauBlueCoeffsRound2 hu
  have hid :
      plateauBlueUpperRound2 z -
          plateauBlueRawUpper (33 / 1000) z =
        (∑ i ∈ Finset.range 22,
          (plateauBlueCoeffsRound2.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (21 - i)) /
          plateauBlueScaleRound2 := by
    dsimp [u, plateauBlueUpperRound2,
      plateauBlueRawUpper, plateauInvOneAddUpper,
      plateauExpPosCoarse, mediumCorrectionPolynomial,
      plateauExpNegUpper, plateauBlueCoeffsRound2,
      plateauBlueScaleRound2, decimalNat]
    norm_num [Finset.sum_range_succ]
    ring
  rw [← sub_nonneg, hid]
  exact div_nonneg h (by
    norm_num [plateauBlueScaleRound2, decimalNat])

lemma tangent_blue_le_round2_plateau {z : ℝ}
    (hz : z ∈ Set.Icc (268 / 1000 : ℝ) (189 / 500)) :
    tangentBlue (33 / 1000) z ≤ plateauBlueUpperRound2 z := by
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hP :
      mediumCorrectionPolynomial (33 / 1000) z ≤ 0 := by
    dsimp [mediumCorrectionPolynomial]
    nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
      mul_nonneg (sq_nonneg z) hzwide.1]
  have hq :
      -mediumCorrectionPolynomial (33 / 1000) z *
          plateauExpNegUpper z ∈ Set.Icc (0 : ℝ) (1 / 5) := by
    have hnegP0 :
        0 ≤ -mediumCorrectionPolynomial (33 / 1000) z := by
      linarith
    have hnegP1 :
        -mediumCorrectionPolynomial (33 / 1000) z ≤ 1 / 5 := by
      have hz3 : z ^ 3 ≤ (2 / 5 : ℝ) ^ 3 := by
        nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
          mul_nonneg (sq_nonneg z) hzwide.1,
          mul_nonneg (sq_nonneg z)
            (sub_nonneg.mpr hzwide.2)]
      dsimp [mediumCorrectionPolynomial]
      nlinarith [hz.1, hz3, sq_nonneg z]
    have he0 : 0 ≤ plateauExpNegUpper z :=
      (Real.exp_pos (-z)).le.trans
        (exp_neg_upper_plateau hzwide)
    have he1 : plateauExpNegUpper z ≤ 1 := by
      have hcoefficient :
          0 ≤ 1 - z / 2 + z ^ 2 / 6 - z ^ 3 / 24 := by
        nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
          mul_nonneg (sq_nonneg z) hzwide.1]
      dsimp [plateauExpNegUpper]
      nlinarith [mul_nonneg hzwide.1 hcoefficient]
    constructor
    · exact mul_nonneg hnegP0 he0
    · calc
        -mediumCorrectionPolynomial (33 / 1000) z *
            plateauExpNegUpper z ≤ (1 / 5 : ℝ) * 1 :=
          mul_le_mul hnegP1 he1 he0 (by norm_num)
        _ = 1 / 5 := by ring
  exact (tangent_blue_le_plateau_raw hzwide hP hq).trans
    (plateau_blue_raw_le_round2 hz)

private def plateauBookDenRound2 (z : ℝ) : ℝ :=
  let B := plateauBlueUpperRound2 z
  let M := plateauMuUpper z
  85262383548455333935963555790500095936000000000000000000000000000000000 *
    (z + 1) ^ 5 * (z + 2) ^ 5 *
    (10000000000 * (1 - B)) *
    (10000000000 * (2 - B)) ^ 3 *
    (24 * (2 - M)) ^ 3 *
    (24 * (1 - M))

set_option maxHeartbeats 0 in
-- Expanding the exact degree-53 rational identity exceeds the default heartbeat budget.
set_option maxRecDepth 10000 in
-- The same rational expansion exceeds the default simplifier recursion depth.
private lemma plateau_book_lower_round2_pos {z : ℝ}
    (hz : z ∈ Set.Icc (268 / 1000 : ℝ) (189 / 500)) :
    0 < plateauBookLower (9 / 200) (33 / 1000)
      plateauBlueUpperRound2 z := by
  let u : ℝ := (1000 * z - 268) / 110
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 53
    plateauBookCoeffsRound2 hu (by
      norm_num [plateauBookCoeffsRound2, decimalNat]) (by
      norm_num [plateauBookCoeffsRound2, decimalNat])
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hblue := tangent_blue_le_round2_plateau hz
  have hblue0 : 0 ≤ tangentBlue (33 / 1000) z := by
    unfold tangentBlue
    exact mul_nonneg hzwide.1 (Real.exp_pos _).le
  have hB0 : 0 ≤ plateauBlueUpperRound2 z :=
    hblue0.trans hblue
  have hz3 : z ^ 3 ≤ (4 / 25 : ℝ) * z := by
    nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
      mul_nonneg (sq_nonneg z) hzwide.1,
      mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hzwide.2)]
  have hB1 : plateauBlueUpperRound2 z < 1 := by
    dsimp [plateauBlueUpperRound2]
    nlinarith [hzwide.1, hzwide.2, hz3, sq_nonneg z,
      pow_nonneg hzwide.1 4]
  have he0 : 0 ≤ plateauExpNegUpper z :=
    (Real.exp_pos (-z)).le.trans (exp_neg_upper_plateau hzwide)
  have he1 : plateauExpNegUpper z ≤ 1 := by
    have hcoef :
        0 ≤ 1 - z / 2 + z ^ 2 / 6 - z ^ 3 / 24 := by
      nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) hzwide.1]
    dsimp [plateauExpNegUpper]
    nlinarith [mul_nonneg hzwide.1 hcoef]
  have hM0 : 0 ≤ plateauMuUpper z := by
    exact mul_nonneg hzwide.1 he0
  have hM1 : plateauMuUpper z < 1 := by
    dsimp [plateauMuUpper]
    nlinarith [mul_le_mul hzwide.2 he1 he0 (by norm_num : (0 : ℝ) ≤ 2 / 5)]
  have hzplus1Pos : 0 < z + 1 := by
    linarith [hzwide.1]
  have hzplus2Pos : 0 < z + 2 := by
    linarith [hzwide.1]
  have hBsub1Pos :
      0 < 1 - plateauBlueUpperRound2 z :=
    sub_pos.mpr hB1
  have hBsub2Pos :
      0 < 2 - plateauBlueUpperRound2 z := by
    linarith
  have hMsub1Pos : 0 < 1 - plateauMuUpper z :=
    sub_pos.mpr hM1
  have hMsub2Pos : 0 < 2 - plateauMuUpper z := by
    linarith
  have hzplus1 := hzplus1Pos.ne'
  have hzplus2 := hzplus2Pos.ne'
  have hBsub1 := hBsub1Pos.ne'
  have hBsub2 := hBsub2Pos.ne'
  have hMsub1 := hMsub1Pos.ne'
  have hMsub2 := hMsub2Pos.ne'
  have hden : 0 < plateauBookDenRound2 z := by
    dsimp [plateauBookDenRound2]
    positivity
  have hid :
      plateauBookLower (9 / 200) (33 / 1000)
          plateauBlueUpperRound2 z =
        ((∑ i ∈ Finset.range 54,
          (plateauBookCoeffsRound2.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (53 - i)) /
          plateauBookScaleRound2) /
          plateauBookDenRound2 z := by
    dsimp only [plateauBookLower, plateauXLogLower]
    rw [medium_log_lower_three_closed (by
        nlinarith [hzwide.1]),
      medium_log_lower_below_one_sub hB0 hB1,
      medium_log_lower_below_one_sub hM0 hM1,
      medium_log_upper_below_closed (by
        nlinarith [hz.1]) (by
        nlinarith [hzwide.1])]
    apply (eq_div_iff hden.ne').2
    calc
      _ = plateauBookPowerRound2
          plateauBookPowerCoeffsRound2 z := by
        dsimp [plateauLogThreeClosed,
          plateauLogLowerBelowOneSub, plateauSumLower,
          plateauBookDenRound2, mediumLogLowerThree,
          mediumLogLowerBelow, mediumLogUpperBelow,
          mediumLogUpperSix, mediumExpNegLower,
          mediumExpNegUpper, KernelBounds.expNegTaylor9,
          KernelBounds.expNegError10]
        norm_num [Nat.factorial]
        field_simp [hzplus1, hzplus2, hBsub1, hBsub2,
          hMsub1, hMsub2]
        dsimp [plateauMuUpper, plateauExpNegUpper,
          plateauBlueUpperRound2, mediumCorrectionPolynomial]
        rw [show 1 + z + 1 = z + 2 by ring]
        field_simp [hzplus1, hzplus2]
        dsimp [plateauBookPowerRound2,
          plateauBookPowerCoeffsRound2, decimalNat]
        ring
      _ = _ := by
        have hBernstein :
            Polynomial.eval₂ (Int.castRingHom ℝ) u
                plateauBookBernsteinPolynomialRound2 =
              ∑ i ∈ Finset.range 54,
                (plateauBookCoeffsRound2.getD i 0 : ℝ) *
                  u ^ i * (1 - u) ^ (53 - i) := by
          dsimp [plateauBookBernsteinPolynomialRound2]
          change
            (Polynomial.eval₂RingHom (Int.castRingHom ℝ) u)
                (∑ i ∈ Finset.range 54,
                  (plateauBookCoeffsRound2.getD i 0 :
                      Polynomial ℤ) *
                    Polynomial.X ^ i *
                      ((1 : Polynomial ℤ) - Polynomial.X) ^
                        (53 - i)) =
              _
          simp [Polynomial.eval₂_pow]
        have hpoly := congrArg
          (Polynomial.eval₂ (Int.castRingHom ℝ) u)
          plateau_book_polynomial_identity_round2
        have hzFromU :
            ((268 + 110 * u) / 1000 : ℝ) = z := by
          dsimp [u]
          ring
        have hhom :=
          eval₂_plateauBookHomogenizedRound2
            plateauBookPowerCoeffsRound2 u
        change
          Polynomial.eval₂ (Int.castRingHom ℝ) u
                (plateauBookHomogenizedRound2
                  plateauBookPowerCoeffsRound2) *
              1000 =
            1000 ^ 54 *
              plateauBookPowerRound2
                plateauBookPowerCoeffsRound2
                ((268 + 110 * u) / 1000) at hhom
        rw [hzFromU] at hhom
        have hhom' :
            Polynomial.eval₂ (Int.castRingHom ℝ) u
                (plateauBookHomogenizedRound2
                  plateauBookPowerCoeffsRound2) =
              1000 ^ 53 *
                plateauBookPowerRound2
                  plateauBookPowerCoeffsRound2 z := by
          apply mul_right_cancel₀
            (by norm_num : (1000 : ℝ) ≠ 0)
          calc
            _ = 1000 ^ 54 *
                plateauBookPowerRound2
                  plateauBookPowerCoeffsRound2 z := hhom
            _ = _ := by ring
        simp only [Polynomial.eval₂_mul,
          Polynomial.eval₂_pow,
          Polynomial.eval₂_ofNat] at hpoly
        rw [hBernstein] at hpoly
        rw [hhom'] at hpoly
        rw [eq_div_iff (by
          norm_num [plateauBookScaleRound2, decimalNat] :
            (plateauBookScaleRound2 : ℝ) ≠ 0)]
        apply mul_left_cancel₀
          (by positivity : (1000 : ℝ) ^ 53 ≠ 0)
        calc
          _ = (plateauBookScaleRound2 : ℝ) *
              (1000 ^ 53 *
                plateauBookPowerRound2
                  plateauBookPowerCoeffsRound2 z) := by
            ring
          _ = _ := by
            simpa using hpoly
  rw [hid]
  exact div_pos
    (div_pos hsum (by
      norm_num [plateauBookScaleRound2, decimalNat]))
    hden

/-- The book inequality on the second-round plateau. -/
lemma tangent_plateau_book_round2 :
    ∀ z ∈ Set.Icc (268 / 1000 : ℝ) (189 / 500),
      0 < tangentCleanBookMargin (33 / 1000) z
        (tangentALog (9 / 200) (99 / 100) +
          tangentBLog (9 / 200) (99 / 100) -
          tangentXLog (33 / 1000) z - Real.log z) := by
  intro z hz
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hblue := tangent_blue_le_round2_plateau hz
  have hblue0 : 0 ≤ tangentBlue (33 / 1000) z := by
    unfold tangentBlue
    exact mul_nonneg hzwide.1 (Real.exp_pos _).le
  have hB0 : 0 ≤ plateauBlueUpperRound2 z :=
    hblue0.trans hblue
  have hB1 : plateauBlueUpperRound2 z < 1 := by
    have hz3 : z ^ 3 ≤ (4 / 25 : ℝ) * z := by
      nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) hzwide.1,
        mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hzwide.2)]
    dsimp [plateauBlueUpperRound2]
    nlinarith [hzwide.1, hzwide.2, hz3, sq_nonneg z,
      pow_nonneg hzwide.1 4]
  have he0 : 0 ≤ plateauExpNegUpper z :=
    (Real.exp_pos (-z)).le.trans (exp_neg_upper_plateau hzwide)
  have he1 : plateauExpNegUpper z ≤ 1 := by
    have hcoef :
        0 ≤ 1 - z / 2 + z ^ 2 / 6 - z ^ 3 / 24 := by
      nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) hzwide.1]
    dsimp [plateauExpNegUpper]
    nlinarith [mul_nonneg hzwide.1 hcoef]
  have hM0 : 0 ≤ plateauMuUpper z :=
    mul_nonneg hzwide.1 he0
  have hM1 : plateauMuUpper z < 1 := by
    dsimp [plateauMuUpper]
    nlinarith [mul_le_mul hzwide.2 he1 he0 (by norm_num : (0 : ℝ) ≤ 2 / 5)]
  exact (plateau_book_lower_round2_pos hz).trans_le
    (plateau_book_lower_le (by norm_num) (by norm_num)
      hzwide (by nlinarith [hz.1]) hB0 hB1 hblue hM0 hM1)

end

end PlateauBookRound2Bounds
end Arxiv2407_19026
