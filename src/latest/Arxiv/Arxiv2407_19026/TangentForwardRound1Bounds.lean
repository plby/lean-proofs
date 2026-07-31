import Arxiv.Arxiv2407_19026.TangentForwardRound1Certificate

/-!
# Semantic first-round forward book bound

This file connects the exact degree-90 polynomial certificate to the analytic
book-margin estimate.
-/

namespace Arxiv2407_19026
namespace ForwardRound1Bounds

noncomputable section

open ForwardRound1Certificate

private def forwardBookDenRound1 (z : ℝ) : ℝ :=
  let t := r1ForwardTReal z
  let B := forwardBlueUpperRound2 z
  let M := plateauMuUpper z
  (6 * 10 ^ 114) *
    (z + 2) ^ 5 *
    (10000000000 * (1 - B)) *
    (10000000000 * (2 - B)) ^ 3 *
    (10000000000000000 * (t + z)) ^ 5 *
    (24 * (2 - M)) ^ 3 *
    (24 * (1 - M))

set_option maxHeartbeats 0 in
-- Normalizing the exact degree-90 Bernstein certificate exceeds the default heartbeat budget.
set_option maxRecDepth 20000 in
-- The expanded rational identity exceeds the default simplifier recursion depth.
private lemma forward_book_lower_round1_pos {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (269 / 1000)) :
    0 < forwardBookLowerRound1 z := by
  let u : ℝ := (1000 * z - 100) / 169
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 90
    forwardBookBernsteinCoeffsRound1 hu (by
      norm_num [forwardBookBernsteinCoeffsRound1,
        decimalNat]) (by
      norm_num [forwardBookBernsteinCoeffsRound1,
        decimalNat])
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hz0 : 0 < z := by nlinarith [hz.1]
  obtain ⟨ht0, ht1, _⟩ := round1_forward_t_bounds hz
  have hblue := tangent_blue_le_round1_forward hz
  have hblue0 : 0 ≤ tangentBlue (9 / 200) z := by
    unfold tangentBlue
    exact mul_nonneg hzwide.1 (Real.exp_pos _).le
  have hB0 : 0 ≤ forwardBlueUpperRound2 z :=
    hblue0.trans hblue
  have hz2 : z ^ 2 ≤ (2 / 5 : ℝ) * z := by
    nlinarith [mul_nonneg hzwide.1
      (sub_nonneg.mpr hzwide.2)]
  have hz3 : z ^ 3 ≤ (4 / 25 : ℝ) * z := by
    nlinarith [hzwide.1, hzwide.2, sq_nonneg z,
      mul_nonneg (sq_nonneg z) hzwide.1,
      mul_nonneg (sq_nonneg z)
        (sub_nonneg.mpr hzwide.2)]
  have hB1 : forwardBlueUpperRound2 z < 1 := by
    dsimp [forwardBlueUpperRound2]
    nlinarith [hzwide.1, hzwide.2, hz2, hz3,
      pow_nonneg hzwide.1 4]
  have he0 : 0 ≤ plateauExpNegUpper z :=
    (Real.exp_pos (-z)).le.trans
      (exp_neg_upper_plateau hzwide)
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
    nlinarith [mul_le_mul hzwide.2 he1 he0
      (by norm_num : (0 : ℝ) ≤ 2 / 5)]
  have hzplus2Pos : 0 < z + 2 := by linarith [hzwide.1]
  have htpluszPos : 0 < r1ForwardTReal z + z := by
    linarith
  have hBsub1Pos : 0 < 1 - forwardBlueUpperRound2 z :=
    sub_pos.mpr hB1
  have hBsub2Pos : 0 < 2 - forwardBlueUpperRound2 z := by
    linarith
  have hMsub1Pos : 0 < 1 - plateauMuUpper z :=
    sub_pos.mpr hM1
  have hMsub2Pos : 0 < 2 - plateauMuUpper z := by
    linarith
  have hratioPlus :
      r1ForwardTReal z / z + 1 ≠ 0 := by
    positivity
  have hden : 0 < forwardBookDenRound1 z := by
    dsimp [forwardBookDenRound1]
    positivity
  have hid :
      forwardBookLowerRound1 z =
        ((∑ i ∈ Finset.range 91,
          (forwardBookBernsteinCoeffsRound1.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (90 - i)) /
          forwardBookScaleRound1) /
          forwardBookDenRound1 z := by
    dsimp only [forwardBookLowerRound1]
    dsimp [plateauXLogLower]
    rw [medium_log_lower_three_closed (by
        linarith [hzwide.1]),
      medium_log_lower_three_closed hratioPlus,
      medium_log_lower_below_one_sub hB0 hB1,
      medium_log_lower_below_one_sub hM0 hM1]
    apply (eq_div_iff hden.ne').2
    calc
      _ = forwardBookPowerRound1
          forwardBookPowerCoeffsRound1 z := by
        dsimp [plateauLogThreeClosed,
          plateauLogLowerBelowOneSub, plateauXLogLower,
          forwardBookDenRound1,
          forwardLogOneAddUpperRound2,
          forwardCorrectionUpperRound1,
          forwardExpNegErrorFive,
          mediumCorrectionPolynomial,
          plateauExpNegUpper,
          KernelBounds.expNegTaylor9,
          KernelBounds.expNegError10]
        norm_num [Nat.factorial]
        field_simp [hz0.ne', hzplus2Pos.ne',
          htpluszPos.ne', hBsub1Pos.ne',
          hBsub2Pos.ne', hMsub1Pos.ne',
          hMsub2Pos.ne']
        dsimp [forwardBlueUpperRound2,
          r1ForwardTReal, tangentLocalPoly,
          tangentRatHorner, TangentAffine.r1ForwardCs,
          forwardBookPowerRound1,
          forwardBookPowerCoeffsRound1, decimalNat]
        dsimp [plateauMuUpper, plateauExpNegUpper]
        ring
      _ = _ := by
        have hBernstein :
            Polynomial.eval₂ (Int.castRingHom ℝ) u
                forwardBookBernsteinPolynomialRound1 =
              ∑ i ∈ Finset.range 91,
                (forwardBookBernsteinCoeffsRound1.getD i 0 : ℝ) *
                  u ^ i * (1 - u) ^ (90 - i) := by
          dsimp [forwardBookBernsteinPolynomialRound1]
          change
            (Polynomial.eval₂RingHom (Int.castRingHom ℝ) u)
                (∑ i ∈ Finset.range 91,
                  (forwardBookBernsteinCoeffsRound1.getD i 0 :
                      Polynomial ℤ) *
                    Polynomial.X ^ i *
                      ((1 : Polynomial ℤ) - Polynomial.X) ^
                        (90 - i)) =
              _
          simp [Polynomial.eval₂_pow]
        have hpoly := congrArg
          (Polynomial.eval₂ (Int.castRingHom ℝ) u)
          forward_book_polynomial_identity_round1
        have hzFromU :
            ((100 + 169 * u) / 1000 : ℝ) = z := by
          dsimp [u]
          ring
        have hhom :=
          eval₂_homogenizedIntegerPolynomialRound1
            forwardBookPowerCoeffsRound1 u
        change
          Polynomial.eval₂ (Int.castRingHom ℝ) u
                (homogenizedIntegerPolynomialRound1
                  forwardBookPowerCoeffsRound1) *
              1000 =
            1000 ^ 91 *
              forwardBookPowerRound1
                forwardBookPowerCoeffsRound1
                ((100 + 169 * u) / 1000) at hhom
        rw [hzFromU] at hhom
        have hhom' :
            Polynomial.eval₂ (Int.castRingHom ℝ) u
                (homogenizedIntegerPolynomialRound1
                  forwardBookPowerCoeffsRound1) =
              1000 ^ 90 *
                forwardBookPowerRound1
                  forwardBookPowerCoeffsRound1 z := by
          apply mul_right_cancel₀
            (by norm_num : (1000 : ℝ) ≠ 0)
          calc
            _ = 1000 ^ 91 *
                forwardBookPowerRound1
                  forwardBookPowerCoeffsRound1 z := hhom
            _ = _ := by ring
        simp only [Polynomial.eval₂_mul,
          Polynomial.eval₂_pow,
          Polynomial.eval₂_ofNat] at hpoly
        rw [hBernstein, hhom'] at hpoly
        rw [eq_div_iff (by
          norm_num [forwardBookScaleRound1, decimalNat] :
            (forwardBookScaleRound1 : ℝ) ≠ 0)]
        apply mul_left_cancel₀
          (by positivity : (1000 : ℝ) ^ 90 ≠ 0)
        calc
          _ = (forwardBookScaleRound1 : ℝ) *
              (1000 ^ 90 *
                forwardBookPowerRound1
                  forwardBookPowerCoeffsRound1 z) := by
            ring
          _ = _ := by
            simpa using hpoly
  rw [hid]
  exact div_pos
    (div_pos hsum (by
      norm_num [forwardBookScaleRound1, decimalNat]))
    hden

/-- The book inequality on the first-round forward interval. -/
lemma tangent_forward_book_round1 :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (269 / 1000),
      0 < tangentCleanBookMargin (9 / 200) z
        (tangentBLog (2 / 25) (r1ForwardTReal z) -
          Real.log z) := by
  intro z hz
  exact (forward_book_lower_round1_pos hz).trans_le
    (forward_book_lower_round1_le hz)

end

end ForwardRound1Bounds
end Arxiv2407_19026
