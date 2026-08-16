import Arxiv.Arxiv2407_19026.TangentForwardCoordRound3Certificate

/-!
# Semantic third-round forward coordinate bound

This file connects the exact degree-65 Bernstein certificate to the analytic
upper and lower bounds for the two logarithmic coordinates.
-/

namespace Arxiv2407_19026
namespace ForwardCoordRound3Bounds

noncomputable section

open ForwardCoordRound3Certificate

private def forwardCoordDenRound3 (z : ℝ) : ℝ :=
  let M := tangentCoordMuLower z
  (1 - M) * (1 + z) ^ 5

set_option maxHeartbeats 0 in
-- The exact degree-65 rational identity exceeds the default heartbeat budget.
set_option maxRecDepth 30000 in
-- Expanding the certified rational functions requires additional recursion depth.
private lemma forward_coord_lower_round3_pos {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250)) :
    0 <
      tangentCoordALogLower (33 / 1000) (r3ForwardTReal z) -
        tangentCoordXLogUpper (3 / 100) z := by
  let u : ℝ := (250 * z - 25) / 42
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 65
    forwardCoordBernsteinCoeffsRound3 hu (by
      norm_num [forwardCoordBernsteinCoeffsRound3,
        decimalNat]) (by
      norm_num [forwardCoordBernsteinCoeffsRound3,
        decimalNat])
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hz0 : 0 < z := by nlinarith [hz.1]
  obtain ⟨ht0, ht1, _⟩ := round3_forward_t_bounds hz
  have ht : r3ForwardTReal z ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨ht0.le, ht1⟩
  have hP :
      mediumCorrectionPolynomial (3 / 100) z ≤ 0 := by
    dsimp [mediumCorrectionPolynomial]
    have hz2 : z ^ 2 ≤ (67 / 250 : ℝ) * z := by
      nlinarith [mul_nonneg hzunit.1
        (sub_nonneg.mpr hz.2)]
    have hz3 : 0 ≤ z ^ 3 :=
      mul_nonneg (sq_nonneg z) hzunit.1
    nlinarith [hz.2]
  have he0 := tangent_coord_exp_lower_nonneg hzunit
  have hq0 :
      0 ≤ tangentCoordSlopeMagnitudeLower (3 / 100) z := by
    unfold tangentCoordSlopeMagnitudeLower
    exact mul_nonneg (neg_nonneg.mpr hP) he0
  have hB0 : 0 ≤ tangentCoordBlueLower (3 / 100) z := by
    unfold tangentCoordBlueLower
    dsimp only
    exact mul_nonneg
      (mul_nonneg hzunit.1
        (inv_nonneg.mpr (by linarith [hzunit.1])))
      (by
        have hq2 := sq_nonneg
          (tangentCoordSlopeMagnitudeLower (3 / 100) z)
        nlinarith [hq0, hq2])
  have hblue := tangent_coord_blue_lower hzunit hP
  have hB1 : tangentCoordBlueLower (3 / 100) z < 1 :=
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
      0 ≤ r3ForwardTReal z ^ 2 *
        (1 / 4 + 33 / 1000 +
          (4 / 25 - 33 / 1000) * r3ForwardTReal z -
          (2 / 25) * r3ForwardTReal z ^ 2) := by
    have hbracket :
        0 ≤ 1 / 4 + 33 / 1000 +
          (4 / 25 - 33 / 1000) * r3ForwardTReal z -
          (2 / 25) * r3ForwardTReal z ^ 2 := by
      nlinarith [ht.1, ht.2, sq_nonneg (r3ForwardTReal z),
        mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
    exact mul_nonneg (sq_nonneg _) hbracket
  have hMsub1 : 0 < 1 - tangentCoordMuLower z :=
    sub_pos.mpr hM1
  have hzplus : 0 < 1 + z := by linarith [hz0]
  have hden : 0 < forwardCoordDenRound3 z := by
    dsimp [forwardCoordDenRound3]
    positivity
  have hrat :
      tangentCoordALogLower (33 / 1000) (r3ForwardTReal z) -
          tangentCoordXLogUpper (3 / 100) z =
        (forwardCoordPowerRound3
            forwardCoordPowerCoeffsRound3 z /
          forwardCoordPowerScaleRound3) /
            forwardCoordDenRound3 z := by
    apply (eq_div_iff hden.ne').2
    unfold tangentCoordALogLower tangentCoordXLogUpper
      forwardCoordDenRound3
    dsimp only
    unfold tangentCoordLogUpper tangentCoordLogUpperBelow
    dsimp only
    field_simp [hMsub1.ne']
    dsimp [tangentCoordBlueLower, tangentCoordMuLower,
      tangentCoordSlopeMagnitudeLower, tangentCoordExpLower,
      tangentCoordALogExpLower, mediumCorrectionPolynomial]
    field_simp [hzplus.ne']
    dsimp [r3ForwardTReal, tangentLocalPoly, tangentRatHorner,
      TangentAffine.r3ForwardCs, forwardCoordPowerRound3,
      forwardCoordPowerCoeffsRound3,
      forwardCoordPowerScaleRound3, decimalNat]
    simp only [evalIntegerPower]
    ring_nf (config := { mode := .raw })
  have hzFromU : ((25 + 42 * u) / 250 : ℝ) = z := by
    dsimp [u]
    ring
  have hscaled := evalIntegerPower_affine_bernstein
    250 65 forwardCoordScaleRound3 25 42
    forwardCoordPowerCoeffsRound3
    forwardCoordBernsteinCoeffsRound3 u
    (by norm_num)
    (by norm_num [forwardCoordPowerCoeffsRound3])
    forward_coord_integer_identity_round3
  norm_num only [Nat.cast_ofNat, Int.cast_ofNat] at hscaled
  rw [hzFromU] at hscaled
  have hpower :
      forwardCoordPowerRound3
          forwardCoordPowerCoeffsRound3 z =
        (∑ i ∈ Finset.range 66,
          (forwardCoordBernsteinCoeffsRound3.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (65 - i)) /
          forwardCoordScaleRound3 := by
    rw [eq_div_iff (by
      norm_num [forwardCoordScaleRound3, decimalNat] :
        (forwardCoordScaleRound3 : ℝ) ≠ 0)]
    simpa [forwardCoordPowerRound3, mul_comm] using hscaled
  rw [hrat, hpower]
  exact div_pos
    (div_pos
      (div_pos (by simpa using hsum) (by
        norm_num [forwardCoordScaleRound3, decimalNat]))
      (by
        norm_num [forwardCoordPowerScaleRound3, decimalNat]))
    hden

/-- The coordinate inequality on the third-round forward interval. -/
lemma tangent_forward_coord_round3 :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      tangentXLog (3 / 100) z ≤
        tangentALog (33 / 1000) (r3ForwardTReal z) := by
  intro z hz
  have hX := tangent_coord_xlog_le
    (β := (3 / 100 : ℝ)) (z := z) (by norm_num)
    (by constructor <;> nlinarith [hz.1, hz.2])
    (by
      dsimp [mediumCorrectionPolynomial]
      nlinarith [hz.1, hz.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) (by nlinarith [hz.1])])
  obtain ⟨ht0, ht1, _⟩ := round3_forward_t_bounds hz
  have hA := tangent_coord_alog_lower_le
    (β := (33 / 1000 : ℝ)) (t := r3ForwardTReal z)
    ⟨ht0.le, ht1⟩ (by
      have hbracket :
          0 ≤ 1 / 4 + 33 / 1000 +
            (4 / 25 - 33 / 1000) * r3ForwardTReal z -
            (2 / 25) * r3ForwardTReal z ^ 2 := by
        nlinarith [ht0, ht1, sq_nonneg (r3ForwardTReal z),
          mul_nonneg ht0.le (sub_nonneg.mpr ht1)]
      exact mul_nonneg (sq_nonneg _) hbracket)
  have hstrict := forward_coord_lower_round3_pos hz
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have he0 := tangent_coord_exp_lower_nonneg hzunit
  have hP :
      mediumCorrectionPolynomial (3 / 100) z ≤ 0 := by
    dsimp [mediumCorrectionPolynomial]
    have hz2 : z ^ 2 ≤ (67 / 250 : ℝ) * z := by
      nlinarith [mul_nonneg hzunit.1
        (sub_nonneg.mpr hz.2)]
    have hz3 : 0 ≤ z ^ 3 :=
      mul_nonneg (sq_nonneg z) hzunit.1
    nlinarith [hz.2]
  have hq0 :
      0 ≤ tangentCoordSlopeMagnitudeLower (3 / 100) z := by
    unfold tangentCoordSlopeMagnitudeLower
    exact mul_nonneg (neg_nonneg.mpr hP) he0
  have hB0 : 0 ≤ tangentCoordBlueLower (3 / 100) z := by
    unfold tangentCoordBlueLower
    dsimp only
    exact mul_nonneg
      (mul_nonneg hzunit.1
        (inv_nonneg.mpr (by linarith [hzunit.1])))
      (by
        have hq2 := sq_nonneg
          (tangentCoordSlopeMagnitudeLower (3 / 100) z)
        nlinarith [hq0, hq2])
  have hblue := tangent_coord_blue_lower hzunit hP
  have hB1 : tangentCoordBlueLower (3 / 100) z < 1 :=
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

end ForwardCoordRound3Bounds
end Arxiv2407_19026
