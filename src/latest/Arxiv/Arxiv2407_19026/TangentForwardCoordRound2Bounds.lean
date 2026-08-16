import Arxiv.Arxiv2407_19026.TangentForwardCoordRound2Certificate

/-!
# Semantic second-round forward coordinate bound

This file connects the exact degree-65 Bernstein certificate to the analytic
upper and lower bounds for the two logarithmic coordinates.
-/

namespace Arxiv2407_19026
namespace ForwardCoordRound2Bounds

noncomputable section

open ForwardCoordRound2Certificate

private def forwardCoordDenRound2 (z : ℝ) : ℝ :=
  let M := tangentCoordMuLower z
  (1 - M) * (1 + z) ^ 5

set_option maxHeartbeats 0 in
-- The exact degree-65 rational identity exceeds the default heartbeat budget.
set_option maxRecDepth 30000 in
-- Expanding the certified rational functions requires additional recursion depth.
private lemma forward_coord_lower_round2_pos {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250)) :
    0 <
      tangentCoordALogLower (9 / 200) (r2ForwardTReal z) -
        tangentCoordXLogUpper (33 / 1000) z := by
  let u : ℝ := (250 * z - 25) / 42
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 65
    forwardCoordBernsteinCoeffsRound2 hu (by
      norm_num [forwardCoordBernsteinCoeffsRound2,
        decimalNat]) (by
      norm_num [forwardCoordBernsteinCoeffsRound2,
        decimalNat])
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hz0 : 0 < z := by nlinarith [hz.1]
  obtain ⟨ht0, ht1, _⟩ := round2_forward_t_bounds hz
  have ht : r2ForwardTReal z ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨ht0.le, ht1⟩
  have hP :
      mediumCorrectionPolynomial (33 / 1000) z ≤ 0 := by
    dsimp [mediumCorrectionPolynomial]
    have hz2 : z ^ 2 ≤ (67 / 250 : ℝ) * z := by
      nlinarith [mul_nonneg hzunit.1
        (sub_nonneg.mpr hz.2)]
    have hz3 : 0 ≤ z ^ 3 :=
      mul_nonneg (sq_nonneg z) hzunit.1
    nlinarith [hz.2]
  have he0 := tangent_coord_exp_lower_nonneg hzunit
  have hq0 :
      0 ≤ tangentCoordSlopeMagnitudeLower (33 / 1000) z := by
    unfold tangentCoordSlopeMagnitudeLower
    exact mul_nonneg (neg_nonneg.mpr hP) he0
  have hB0 : 0 ≤ tangentCoordBlueLower (33 / 1000) z := by
    unfold tangentCoordBlueLower
    dsimp only
    exact mul_nonneg
      (mul_nonneg hzunit.1
        (inv_nonneg.mpr (by linarith [hzunit.1])))
      (by
        have hq2 := sq_nonneg
          (tangentCoordSlopeMagnitudeLower (33 / 1000) z)
        nlinarith [hq0, hq2])
  have hblue := tangent_coord_blue_lower hzunit hP
  have hB1 : tangentCoordBlueLower (33 / 1000) z < 1 :=
    hblue.trans_lt (tangentBlue_lt_one (by norm_num) hzunit.1 hzunit.2)
  have hM0 : 0 ≤ tangentCoordMuLower z := by
    unfold tangentCoordMuLower
    exact mul_nonneg hzunit.1 he0
  have he1 : tangentCoordExpLower z ≤ 1 := by
    dsimp [tangentCoordExpLower]
    have hz2 : z ^ 2 ≤ z := by
      nlinarith [mul_nonneg hzunit.1
        (sub_nonneg.mpr hzunit.2)]
    have hz3 : 0 ≤ z ^ 3 :=
      mul_nonneg (sq_nonneg z) hzunit.1
    nlinarith
  have hM1 : tangentCoordMuLower z < 1 := by
    unfold tangentCoordMuLower
    have hmul := mul_le_mul hz.2 he1 he0 (by norm_num :
      (0 : ℝ) ≤ 67 / 250)
    nlinarith
  have hcoefficient :
      0 ≤ r2ForwardTReal z ^ 2 *
        (1 / 4 + 9 / 200 +
          (4 / 25 - 9 / 200) * r2ForwardTReal z -
          (2 / 25) * r2ForwardTReal z ^ 2) := by
    have hbracket :
        0 ≤ 1 / 4 + 9 / 200 +
          (4 / 25 - 9 / 200) * r2ForwardTReal z -
          (2 / 25) * r2ForwardTReal z ^ 2 := by
      nlinarith [ht.1, ht.2, sq_nonneg (r2ForwardTReal z),
        mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
    exact mul_nonneg (sq_nonneg _) hbracket
  have hMsub1 : 0 < 1 - tangentCoordMuLower z :=
    sub_pos.mpr hM1
  have hzplus : 0 < 1 + z := by linarith [hz0]
  have hden : 0 < forwardCoordDenRound2 z := by
    dsimp [forwardCoordDenRound2]
    positivity
  have hrat :
      tangentCoordALogLower (9 / 200) (r2ForwardTReal z) -
          tangentCoordXLogUpper (33 / 1000) z =
        (forwardCoordPowerRound2
            forwardCoordPowerCoeffsRound2 z /
          forwardCoordPowerScaleRound2) /
            forwardCoordDenRound2 z := by
    apply (eq_div_iff hden.ne').2
    unfold tangentCoordALogLower tangentCoordXLogUpper
      forwardCoordDenRound2
    dsimp only
    unfold tangentCoordLogUpper tangentCoordLogUpperBelow
    dsimp only
    field_simp [hMsub1.ne']
    dsimp [tangentCoordBlueLower, tangentCoordMuLower,
      tangentCoordSlopeMagnitudeLower, tangentCoordExpLower,
      tangentCoordALogExpLower, mediumCorrectionPolynomial]
    field_simp [hzplus.ne']
    dsimp [r2ForwardTReal, tangentLocalPoly, tangentRatHorner,
      TangentAffine.r2ForwardCs, forwardCoordPowerRound2,
      forwardCoordPowerCoeffsRound2,
      forwardCoordPowerScaleRound2, decimalNat]
    simp only [evalIntegerPower]
    ring_nf (config := { mode := .raw })
  have hzFromU : ((25 + 42 * u) / 250 : ℝ) = z := by
    dsimp [u]
    ring
  have hscaled := evalIntegerPower_affine_bernstein
    250 65 forwardCoordScaleRound2 25 42
    forwardCoordPowerCoeffsRound2
    forwardCoordBernsteinCoeffsRound2 u
    (by norm_num)
    (by norm_num [forwardCoordPowerCoeffsRound2])
    forward_coord_integer_identity_round2
  norm_num only [Nat.cast_ofNat, Int.cast_ofNat] at hscaled
  rw [hzFromU] at hscaled
  have hpower :
      forwardCoordPowerRound2
          forwardCoordPowerCoeffsRound2 z =
        (∑ i ∈ Finset.range 66,
          (forwardCoordBernsteinCoeffsRound2.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (65 - i)) /
          forwardCoordScaleRound2 := by
    rw [eq_div_iff (by
      norm_num [forwardCoordScaleRound2, decimalNat] :
        (forwardCoordScaleRound2 : ℝ) ≠ 0)]
    simpa [forwardCoordPowerRound2, mul_comm] using hscaled
  rw [hrat, hpower]
  exact div_pos
    (div_pos
      (div_pos (by simpa using hsum) (by
        norm_num [forwardCoordScaleRound2, decimalNat]))
      (by
        norm_num [forwardCoordPowerScaleRound2, decimalNat]))
    hden

/-- The coordinate inequality on the second-round forward interval. -/
lemma tangent_forward_coord_round2 :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      tangentXLog (33 / 1000) z ≤
        tangentALog (9 / 200) (r2ForwardTReal z) := by
  intro z hz
  have hX := tangent_coord_xlog_le
    (β := (33 / 1000 : ℝ)) (z := z) (by norm_num)
    (by constructor <;> nlinarith [hz.1, hz.2])
    (by
      dsimp [mediumCorrectionPolynomial]
      nlinarith [hz.1, hz.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) (by nlinarith [hz.1])])
  obtain ⟨ht0, ht1, _⟩ := round2_forward_t_bounds hz
  have hA := tangent_coord_alog_lower_le
    (β := (9 / 200 : ℝ)) (t := r2ForwardTReal z)
    ⟨ht0.le, ht1⟩ (by
      have hbracket :
          0 ≤ 1 / 4 + 9 / 200 +
            (4 / 25 - 9 / 200) * r2ForwardTReal z -
            (2 / 25) * r2ForwardTReal z ^ 2 := by
        nlinarith [ht0, ht1, sq_nonneg (r2ForwardTReal z),
          mul_nonneg ht0.le (sub_nonneg.mpr ht1)]
      exact mul_nonneg (sq_nonneg _) hbracket)
  have hstrict := forward_coord_lower_round2_pos hz
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have he0 := tangent_coord_exp_lower_nonneg hzunit
  have hP :
      mediumCorrectionPolynomial (33 / 1000) z ≤ 0 := by
    dsimp [mediumCorrectionPolynomial]
    have hz2 : z ^ 2 ≤ (67 / 250 : ℝ) * z := by
      nlinarith [mul_nonneg hzunit.1
        (sub_nonneg.mpr hz.2)]
    have hz3 : 0 ≤ z ^ 3 :=
      mul_nonneg (sq_nonneg z) hzunit.1
    nlinarith [hz.2]
  have hq0 :
      0 ≤ tangentCoordSlopeMagnitudeLower (33 / 1000) z := by
    unfold tangentCoordSlopeMagnitudeLower
    exact mul_nonneg (neg_nonneg.mpr hP) he0
  have hB0 : 0 ≤ tangentCoordBlueLower (33 / 1000) z := by
    unfold tangentCoordBlueLower
    dsimp only
    exact mul_nonneg
      (mul_nonneg hzunit.1
        (inv_nonneg.mpr (by linarith [hzunit.1])))
      (by
        have hq2 := sq_nonneg
          (tangentCoordSlopeMagnitudeLower (33 / 1000) z)
        nlinarith [hq0, hq2])
  have hblue := tangent_coord_blue_lower hzunit hP
  have hB1 : tangentCoordBlueLower (33 / 1000) z < 1 :=
    hblue.trans_lt (tangentBlue_lt_one (by norm_num)
      hzunit.1 hzunit.2)
  have hM0 : 0 ≤ tangentCoordMuLower z := by
    unfold tangentCoordMuLower
    exact mul_nonneg hzunit.1 he0
  have he1 : tangentCoordExpLower z ≤ 1 := by
    dsimp [tangentCoordExpLower]
    have hz2 : z ^ 2 ≤ z := by
      nlinarith [mul_nonneg hzunit.1
        (sub_nonneg.mpr hzunit.2)]
    have hz3 : 0 ≤ z ^ 3 :=
      mul_nonneg (sq_nonneg z) hzunit.1
    nlinarith
  have hM1 : tangentCoordMuLower z < 1 := by
    unfold tangentCoordMuLower
    have hmul := mul_le_mul hz.2 he1 he0 (by norm_num :
      (0 : ℝ) ≤ 67 / 250)
    nlinarith
  have hX' := hX hB0 hB1 hM0 hM1
  linarith

end

end ForwardCoordRound2Bounds
end Arxiv2407_19026
