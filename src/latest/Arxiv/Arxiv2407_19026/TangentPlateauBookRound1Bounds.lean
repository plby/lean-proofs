import Arxiv.Arxiv2407_19026.TangentPlateauBookRound1Certificate

/-!
# Semantic first-round plateau book bound

This file connects the degree-53 exact certificate to the analytic
plateau-book lower bound.
-/

namespace Arxiv2407_19026
namespace PlateauBookRound1Bounds

noncomputable section

open PlateauBookRound1Certificate

def plateauBlueUpperRound1 (z : ℝ) : ℝ :=
  -(2654621873 / 10000000000) * z ^ 4 +
    2534114217 / 2000000000 * z ^ 3 -
    16653304303 / 10000000000 * z ^ 2 +
    3066432097 / 2500000000 * z +
    6966917 / 1250000000

private lemma plateau_blue_raw_le_round1 {z : ℝ}
    (hz : z ∈ Set.Icc (269 / 1000 : ℝ) (387 / 1000)) :
    plateauBlueRawUpper (9 / 200) z ≤
      plateauBlueUpperRound1 z := by
  let u : ℝ := (1000 * z - 269) / 118
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have h := KernelBounds.bernstein_sum_nonneg 21
    plateauBlueCoeffsRound1 hu
  have hid :
      plateauBlueUpperRound1 z -
          plateauBlueRawUpper (9 / 200) z =
        (∑ i ∈ Finset.range 22,
          (plateauBlueCoeffsRound1.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (21 - i)) /
          plateauBlueScaleRound1 := by
    dsimp [u, plateauBlueUpperRound1,
      plateauBlueRawUpper, plateauInvOneAddUpper,
      plateauExpPosCoarse, mediumCorrectionPolynomial,
      plateauExpNegUpper, plateauBlueCoeffsRound1,
      plateauBlueScaleRound1, decimalNat]
    norm_num [Finset.sum_range_succ]
    ring
  rw [← sub_nonneg, hid]
  exact div_nonneg h (by
    norm_num [plateauBlueScaleRound1, decimalNat])

lemma tangent_blue_le_round1_plateau {z : ℝ}
    (hz : z ∈ Set.Icc (269 / 1000 : ℝ) (387 / 1000)) :
    tangentBlue (9 / 200) z ≤ plateauBlueUpperRound1 z := by
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hP :
      mediumCorrectionPolynomial (9 / 200) z ≤ 0 := by
    dsimp [mediumCorrectionPolynomial]
    nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
      mul_nonneg (sq_nonneg z) hzwide.1]
  have hq :
      -mediumCorrectionPolynomial (9 / 200) z *
          plateauExpNegUpper z ∈ Set.Icc (0 : ℝ) (1 / 5) := by
    have hnegP0 :
        0 ≤ -mediumCorrectionPolynomial (9 / 200) z := by
      linarith
    have hnegP1 :
        -mediumCorrectionPolynomial (9 / 200) z ≤ 1 / 5 := by
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
        -mediumCorrectionPolynomial (9 / 200) z *
            plateauExpNegUpper z ≤ (1 / 5 : ℝ) * 1 :=
          mul_le_mul hnegP1 he1 he0 (by norm_num)
        _ = 1 / 5 := by ring
  exact (tangent_blue_le_plateau_raw hzwide hP hq).trans
    (plateau_blue_raw_le_round1 hz)

private def plateauBookDenRound1 (z : ℝ) : ℝ :=
  let B := plateauBlueUpperRound1 z
  let M := plateauMuUpper z
  21315595887113833483990888947625023984000000000000000000000000000000000 *
    (z + 1) ^ 5 * (z + 2) ^ 5 *
    (10000000000 * (1 - B)) *
    (10000000000 * (2 - B)) ^ 3 *
    (24 * (2 - M)) ^ 3 *
    (24 * (1 - M))

set_option maxHeartbeats 0 in
-- Expanding the exact degree-53 rational identity exceeds the default heartbeat budget.
set_option maxRecDepth 10000 in
-- The same rational expansion exceeds the default simplifier recursion depth.
private lemma plateau_book_lower_round1_pos {z : ℝ}
    (hz : z ∈ Set.Icc (269 / 1000 : ℝ) (387 / 1000)) :
    0 < plateauBookLower (2 / 25) (9 / 200)
      plateauBlueUpperRound1 z := by
  let u : ℝ := (1000 * z - 269) / 118
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 53
    plateauBookCoeffsRound1 hu (by
      norm_num [plateauBookCoeffsRound1, decimalNat]) (by
      norm_num [plateauBookCoeffsRound1, decimalNat])
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hblue := tangent_blue_le_round1_plateau hz
  have hblue0 : 0 ≤ tangentBlue (9 / 200) z := by
    unfold tangentBlue
    exact mul_nonneg hzwide.1 (Real.exp_pos _).le
  have hB0 : 0 ≤ plateauBlueUpperRound1 z :=
    hblue0.trans hblue
  have hz3 : z ^ 3 ≤ (4 / 25 : ℝ) * z := by
    nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
      mul_nonneg (sq_nonneg z) hzwide.1,
      mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hzwide.2)]
  have hB1 : plateauBlueUpperRound1 z < 1 := by
    dsimp [plateauBlueUpperRound1]
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
      0 < 1 - plateauBlueUpperRound1 z :=
    sub_pos.mpr hB1
  have hBsub2Pos :
      0 < 2 - plateauBlueUpperRound1 z := by
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
  have hden : 0 < plateauBookDenRound1 z := by
    dsimp [plateauBookDenRound1]
    positivity
  have hid :
      plateauBookLower (2 / 25) (9 / 200)
          plateauBlueUpperRound1 z =
        ((∑ i ∈ Finset.range 54,
          (plateauBookCoeffsRound1.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (53 - i)) /
          plateauBookScaleRound1) /
          plateauBookDenRound1 z := by
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
      _ = plateauBookPowerRound1
          plateauBookPowerCoeffsRound1 z := by
        dsimp [plateauLogThreeClosed,
          plateauLogLowerBelowOneSub, plateauSumLower,
          plateauBookDenRound1, mediumLogLowerThree,
          mediumLogLowerBelow, mediumLogUpperBelow,
          mediumLogUpperSix, mediumExpNegLower,
          mediumExpNegUpper, KernelBounds.expNegTaylor9,
          KernelBounds.expNegError10]
        norm_num [Nat.factorial]
        field_simp [hzplus1, hzplus2, hBsub1, hBsub2,
          hMsub1, hMsub2]
        dsimp [plateauMuUpper, plateauExpNegUpper,
          plateauBlueUpperRound1, mediumCorrectionPolynomial]
        rw [show 1 + z + 1 = z + 2 by ring]
        field_simp [hzplus1, hzplus2]
        dsimp [plateauBookPowerRound1,
          plateauBookPowerCoeffsRound1, decimalNat]
        ring
      _ = _ := by
        have hBernstein :
            Polynomial.eval₂ (Int.castRingHom ℝ) u
                plateauBookBernsteinPolynomialRound1 =
              ∑ i ∈ Finset.range 54,
                (plateauBookCoeffsRound1.getD i 0 : ℝ) *
                  u ^ i * (1 - u) ^ (53 - i) := by
          dsimp [plateauBookBernsteinPolynomialRound1]
          change
            (Polynomial.eval₂RingHom (Int.castRingHom ℝ) u)
                (∑ i ∈ Finset.range 54,
                  (plateauBookCoeffsRound1.getD i 0 :
                      Polynomial ℤ) *
                    Polynomial.X ^ i *
                      ((1 : Polynomial ℤ) - Polynomial.X) ^
                        (53 - i)) =
              _
          simp [Polynomial.eval₂_pow]
        have hpoly := congrArg
          (Polynomial.eval₂ (Int.castRingHom ℝ) u)
          plateau_book_polynomial_identity_round1
        have hzFromU :
            ((269 + 118 * u) / 1000 : ℝ) = z := by
          dsimp [u]
          ring
        have hhom :=
          eval₂_plateauBookHomogenizedRound1
            plateauBookPowerCoeffsRound1 u
        change
          Polynomial.eval₂ (Int.castRingHom ℝ) u
                (plateauBookHomogenizedRound1
                  plateauBookPowerCoeffsRound1) *
              1000 =
            1000 ^ 54 *
              plateauBookPowerRound1
                plateauBookPowerCoeffsRound1
                ((269 + 118 * u) / 1000) at hhom
        rw [hzFromU] at hhom
        have hhom' :
            Polynomial.eval₂ (Int.castRingHom ℝ) u
                (plateauBookHomogenizedRound1
                  plateauBookPowerCoeffsRound1) =
              1000 ^ 53 *
                plateauBookPowerRound1
                  plateauBookPowerCoeffsRound1 z := by
          apply mul_right_cancel₀
            (by norm_num : (1000 : ℝ) ≠ 0)
          calc
            _ = 1000 ^ 54 *
                plateauBookPowerRound1
                  plateauBookPowerCoeffsRound1 z := hhom
            _ = _ := by ring
        simp only [Polynomial.eval₂_mul,
          Polynomial.eval₂_pow,
          Polynomial.eval₂_ofNat] at hpoly
        rw [hBernstein] at hpoly
        rw [hhom'] at hpoly
        rw [eq_div_iff (by
          norm_num [plateauBookScaleRound1, decimalNat] :
            (plateauBookScaleRound1 : ℝ) ≠ 0)]
        apply mul_left_cancel₀
          (by positivity : (1000 : ℝ) ^ 53 ≠ 0)
        calc
          _ = (plateauBookScaleRound1 : ℝ) *
              (1000 ^ 53 *
                plateauBookPowerRound1
                  plateauBookPowerCoeffsRound1 z) := by
            ring
          _ = _ := by
            simpa using hpoly
  rw [hid]
  exact div_pos
    (div_pos hsum (by
      norm_num [plateauBookScaleRound1, decimalNat]))
    hden

/-- The book inequality on the first-round plateau. -/
lemma tangent_plateau_book_round1 :
    ∀ z ∈ Set.Icc (269 / 1000 : ℝ) (387 / 1000),
      0 < tangentCleanBookMargin (9 / 200) z
        (tangentALog (2 / 25) (99 / 100) +
          tangentBLog (2 / 25) (99 / 100) -
          tangentXLog (9 / 200) z - Real.log z) := by
  intro z hz
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hblue := tangent_blue_le_round1_plateau hz
  have hblue0 : 0 ≤ tangentBlue (9 / 200) z := by
    unfold tangentBlue
    exact mul_nonneg hzwide.1 (Real.exp_pos _).le
  have hB0 : 0 ≤ plateauBlueUpperRound1 z :=
    hblue0.trans hblue
  have hB1 : plateauBlueUpperRound1 z < 1 := by
    have hz3 : z ^ 3 ≤ (4 / 25 : ℝ) * z := by
      nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) hzwide.1,
        mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hzwide.2)]
    dsimp [plateauBlueUpperRound1]
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
  exact (plateau_book_lower_round1_pos hz).trans_le
    (plateau_book_lower_le (by norm_num) (by norm_num)
      hzwide (by nlinarith [hz.1]) hB0 hB1 hblue hM0 hM1)

end

end PlateauBookRound1Bounds
end Arxiv2407_19026
