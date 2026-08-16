import Arxiv.Arxiv2407_19026.TangentForwardRound2Certificate

/-!
# Semantic second-round forward book bound

This file connects the exact degree-90 polynomial certificate to the analytic
book-margin estimate.
-/

namespace Arxiv2407_19026
namespace ForwardRound2Bounds

noncomputable section

open ForwardRound2Certificate

private def forwardBookDenRound2 (z : ℝ) : ℝ :=
  let t := r2ForwardTReal z
  let B := forwardBlueUpperRound2 z
  let M := plateauMuUpper z
  (46875 * 10 ^ 108) *
    (z + 2) ^ 5 *
    (10000000000 * (1 - B)) *
    (10000000000 * (2 - B)) ^ 3 *
    (5000000000000000 * (t + z)) ^ 5 *
    (24 * (2 - M)) ^ 3 *
    (24 * (1 - M))

set_option maxHeartbeats 0 in
-- Normalizing the exact degree-90 Bernstein certificate exceeds the default heartbeat budget.
set_option maxRecDepth 20000 in
-- The expanded rational identity exceeds the default simplifier recursion depth.
private lemma forward_book_lower_round2_pos {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250)) :
    0 < forwardBookLowerRound2 z := by
  let u : ℝ := (250 * z - 25) / 42
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 90
    forwardBookBernsteinCoeffsRound2 hu
      forward_book_bernstein_first_pos_round2
      forward_book_bernstein_last_pos_round2
  have hzwide : z ∈ Set.Icc (0 : ℝ) (2 / 5) := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hz0 : 0 < z := by nlinarith [hz.1]
  obtain ⟨ht0, ht1, _⟩ := round2_forward_t_bounds hz
  have hblue := tangent_blue_le_round2_forward hz
  have hblue0 : 0 ≤ tangentBlue (33 / 1000) z := by
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
  have htpluszPos : 0 < r2ForwardTReal z + z := by
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
      r2ForwardTReal z / z + 1 ≠ 0 := by
    positivity
  have hden : 0 < forwardBookDenRound2 z := by
    dsimp [forwardBookDenRound2]
    positivity
  have hid :
      forwardBookLowerRound2 z =
        ((∑ i ∈ Finset.range 91,
          (forwardBookBernsteinCoeffsRound2.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (90 - i)) /
          forwardBookScaleRound2) /
          forwardBookDenRound2 z := by
    dsimp only [forwardBookLowerRound2]
    dsimp [plateauXLogLower]
    rw [medium_log_lower_three_closed (by
        linarith [hzwide.1]),
      medium_log_lower_three_closed hratioPlus,
      medium_log_lower_below_one_sub hB0 hB1,
      medium_log_lower_below_one_sub hM0 hM1]
    apply (eq_div_iff hden.ne').2
    calc
      _ = forwardBookPowerRound2
          forwardBookPowerCoeffsRound2 z := by
        dsimp [plateauLogThreeClosed,
          plateauLogLowerBelowOneSub, plateauXLogLower,
          forwardBookDenRound2,
          forwardLogOneAddUpperRound2,
          forwardCorrectionUpperRound2,
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
          r2ForwardTReal, tangentLocalPoly,
          tangentRatHorner, TangentAffine.r2ForwardCs,
          forwardBookPowerRound2,
          forwardBookPowerCoeffsRound2, evalIntegerPower,
          decimalNat]
        dsimp [plateauMuUpper, plateauExpNegUpper]
        ring_nf (config := { mode := .raw })
      _ = _ := by
        have hidentity :=
          forward_book_bernstein_identity_round2 u
        have hzFromU :
            ((25 + 42 * u) / 250 : ℝ) = z := by
          dsimp [u]
          ring
        rw [hzFromU] at hidentity
        rw [eq_div_iff (by
          exact_mod_cast forward_book_scale_pos_round2.ne' :
            (forwardBookScaleRound2 : ℝ) ≠ 0)]
        simpa [mul_comm] using hidentity
  rw [hid]
  exact div_pos
    (div_pos hsum (by
      exact_mod_cast forward_book_scale_pos_round2))
    hden

/-- The book inequality on the second-round forward interval. -/
lemma tangent_forward_book_round2 :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      0 < tangentCleanBookMargin (33 / 1000) z
        (tangentBLog (9 / 200) (r2ForwardTReal z) -
          Real.log z) := by
  intro z hz
  exact (forward_book_lower_round2_pos hz).trans_le
    (forward_book_lower_round2_le hz)

end

end ForwardRound2Bounds
end Arxiv2407_19026
