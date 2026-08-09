import Arxiv.Arxiv2407_19026.TangentForwardCoordRound1Certificate

/-!
# Semantic first-round forward coordinate bound

This file connects the exact degree-65 Bernstein certificate to the analytic
upper and lower bounds for the two logarithmic coordinates.
-/

namespace Arxiv2407_19026
namespace ForwardCoordRound1Bounds

noncomputable section

open ForwardCoordRound1Certificate

private def forwardCoordDenRound1 (z : ℝ) : ℝ :=
  let M := tangentCoordMuLower z
  (1 - M) * (1 + z) ^ 5

set_option maxHeartbeats 0 in
-- The exact degree-65 rational identity exceeds the default heartbeat budget.
set_option maxRecDepth 30000 in
-- Expanding the certified rational functions requires additional recursion depth.
private lemma forward_coord_lower_round1_pos {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (269 / 1000)) :
    0 <
      tangentCoordALogLower (2 / 25) (r1ForwardTReal z) -
        tangentCoordXLogUpper (9 / 200) z := by
  let u : ℝ := (1000 * z - 100) / 169
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 65
    forwardCoordBernsteinCoeffsRound1 hu (by
      norm_num [forwardCoordBernsteinCoeffsRound1,
        decimalNat]) (by
      norm_num [forwardCoordBernsteinCoeffsRound1,
        decimalNat])
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hz0 : 0 < z := by nlinarith [hz.1]
  obtain ⟨ht0, ht1, _⟩ := round1_forward_t_bounds hz
  have ht : r1ForwardTReal z ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨ht0.le, ht1⟩
  have hP :
      mediumCorrectionPolynomial (9 / 200) z ≤ 0 := by
    dsimp [mediumCorrectionPolynomial]
    have hz2 : z ^ 2 ≤ (269 / 1000 : ℝ) * z := by
      nlinarith [mul_nonneg hzunit.1
        (sub_nonneg.mpr hz.2)]
    have hz3 : 0 ≤ z ^ 3 :=
      mul_nonneg (sq_nonneg z) hzunit.1
    nlinarith [hz.2]
  have he0 := tangent_coord_exp_lower_nonneg hzunit
  have hq0 :
      0 ≤ tangentCoordSlopeMagnitudeLower (9 / 200) z := by
    unfold tangentCoordSlopeMagnitudeLower
    exact mul_nonneg (neg_nonneg.mpr hP) he0
  have hB0 : 0 ≤ tangentCoordBlueLower (9 / 200) z := by
    unfold tangentCoordBlueLower
    dsimp only
    exact mul_nonneg
      (mul_nonneg hzunit.1
        (inv_nonneg.mpr (by linarith [hzunit.1])))
      (by
        have hq2 := sq_nonneg
          (tangentCoordSlopeMagnitudeLower (9 / 200) z)
        nlinarith [hq0, hq2])
  have hblue := tangent_coord_blue_lower hzunit hP
  have hB1 : tangentCoordBlueLower (9 / 200) z < 1 :=
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
      (0 : ℝ) ≤ 269 / 1000)
    nlinarith
  have hcoefficient :
      0 ≤ r1ForwardTReal z ^ 2 *
        (1 / 4 + 2 / 25 +
          (4 / 25 - 2 / 25) * r1ForwardTReal z -
          (2 / 25) * r1ForwardTReal z ^ 2) := by
    have hbracket :
        0 ≤ 1 / 4 + 2 / 25 +
          (4 / 25 - 2 / 25) * r1ForwardTReal z -
          (2 / 25) * r1ForwardTReal z ^ 2 := by
      nlinarith [ht.1, ht.2, sq_nonneg (r1ForwardTReal z),
        mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
    exact mul_nonneg (sq_nonneg _) hbracket
  have hMsub1 : 0 < 1 - tangentCoordMuLower z :=
    sub_pos.mpr hM1
  have hzplus : 0 < 1 + z := by linarith [hz0]
  have hden : 0 < forwardCoordDenRound1 z := by
    dsimp [forwardCoordDenRound1]
    positivity
  have hrat :
      tangentCoordALogLower (2 / 25) (r1ForwardTReal z) -
          tangentCoordXLogUpper (9 / 200) z =
        (forwardCoordPowerRound1
            forwardCoordPowerCoeffsRound1 z /
          forwardCoordPowerScaleRound1) /
            forwardCoordDenRound1 z := by
    apply (eq_div_iff hden.ne').2
    unfold tangentCoordALogLower tangentCoordXLogUpper
      forwardCoordDenRound1
    dsimp only
    unfold tangentCoordLogUpper tangentCoordLogUpperBelow
    dsimp only
    field_simp [hMsub1.ne']
    dsimp [tangentCoordBlueLower, tangentCoordMuLower,
      tangentCoordSlopeMagnitudeLower, tangentCoordExpLower,
      tangentCoordALogExpLower, mediumCorrectionPolynomial]
    field_simp [hzplus.ne']
    dsimp [r1ForwardTReal, tangentLocalPoly, tangentRatHorner,
      TangentAffine.r1ForwardCs, forwardCoordPowerRound1,
      forwardCoordPowerCoeffsRound1,
      forwardCoordPowerScaleRound1, decimalNat]
    ring
  have hBernstein :
      Polynomial.eval₂ (Int.castRingHom ℝ) u
          forwardCoordBernsteinPolynomialRound1 =
        ∑ i ∈ Finset.range 66,
          (forwardCoordBernsteinCoeffsRound1.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (65 - i) := by
    dsimp [forwardCoordBernsteinPolynomialRound1]
    change
      (Polynomial.eval₂RingHom (Int.castRingHom ℝ) u)
          (∑ i ∈ Finset.range 66,
            (forwardCoordBernsteinCoeffsRound1.getD i 0 :
                Polynomial ℤ) *
              Polynomial.X ^ i *
                ((1 : Polynomial ℤ) - Polynomial.X) ^
                  (65 - i)) =
        _
    simp [Polynomial.eval₂_pow]
  have hpoly := congrArg
    (Polynomial.eval₂ (Int.castRingHom ℝ) u)
    forward_coord_polynomial_identity_round1
  have hzFromU : ((100 + 169 * u) / 1000 : ℝ) = z := by
    dsimp [u]
    ring
  have hhom :=
    eval₂_forwardCoordHomogenizedRound1
      forwardCoordPowerCoeffsRound1 u
  change
    Polynomial.eval₂ (Int.castRingHom ℝ) u
          (forwardCoordHomogenizedRound1
            forwardCoordPowerCoeffsRound1) *
        1000 =
      1000 ^ 66 *
        forwardCoordPowerRound1
          forwardCoordPowerCoeffsRound1
          ((100 + 169 * u) / 1000) at hhom
  rw [hzFromU] at hhom
  have hhom' :
      Polynomial.eval₂ (Int.castRingHom ℝ) u
          (forwardCoordHomogenizedRound1
            forwardCoordPowerCoeffsRound1) =
        1000 ^ 65 *
          forwardCoordPowerRound1
            forwardCoordPowerCoeffsRound1 z := by
    apply mul_right_cancel₀ (by norm_num : (1000 : ℝ) ≠ 0)
    calc
      _ = 1000 ^ 66 *
          forwardCoordPowerRound1
            forwardCoordPowerCoeffsRound1 z := hhom
      _ = _ := by ring
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_ofNat] at hpoly
  rw [hBernstein, hhom'] at hpoly
  have hpower :
      forwardCoordPowerRound1
          forwardCoordPowerCoeffsRound1 z =
        (∑ i ∈ Finset.range 66,
          (forwardCoordBernsteinCoeffsRound1.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (65 - i)) /
          forwardCoordScaleRound1 := by
    rw [eq_div_iff (by
      norm_num [forwardCoordScaleRound1, decimalNat] :
        (forwardCoordScaleRound1 : ℝ) ≠ 0)]
    apply mul_left_cancel₀
      (by positivity : (1000 : ℝ) ^ 65 ≠ 0)
    calc
      _ = (forwardCoordScaleRound1 : ℝ) *
          (1000 ^ 65 *
            forwardCoordPowerRound1
              forwardCoordPowerCoeffsRound1 z) := by
        ring
      _ = _ := by
        simpa using hpoly
  rw [hrat, hpower]
  exact div_pos
    (div_pos
      (div_pos (by simpa using hsum) (by
        norm_num [forwardCoordScaleRound1, decimalNat]))
      (by
        norm_num [forwardCoordPowerScaleRound1, decimalNat]))
    hden

/-- The coordinate inequality on the first-round forward interval. -/
lemma tangent_forward_coord_round1 :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (269 / 1000),
      tangentXLog (9 / 200) z ≤
        tangentALog (2 / 25) (r1ForwardTReal z) := by
  intro z hz
  have hX := tangent_coord_xlog_le
    (β := (9 / 200 : ℝ)) (z := z) (by norm_num)
    (by constructor <;> nlinarith [hz.1, hz.2])
    (by
      dsimp [mediumCorrectionPolynomial]
      nlinarith [hz.1, hz.2, sq_nonneg z,
        mul_nonneg (sq_nonneg z) (by nlinarith [hz.1])])
  obtain ⟨ht0, ht1, _⟩ := round1_forward_t_bounds hz
  have hA := tangent_coord_alog_lower_le
    (β := (2 / 25 : ℝ)) (t := r1ForwardTReal z)
    ⟨ht0.le, ht1⟩ (by
      have hbracket :
          0 ≤ 1 / 4 + 2 / 25 +
            (4 / 25 - 2 / 25) * r1ForwardTReal z -
            (2 / 25) * r1ForwardTReal z ^ 2 := by
        nlinarith [ht0, ht1, sq_nonneg (r1ForwardTReal z),
          mul_nonneg ht0.le (sub_nonneg.mpr ht1)]
      exact mul_nonneg (sq_nonneg _) hbracket)
  have hstrict := forward_coord_lower_round1_pos hz
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have he0 := tangent_coord_exp_lower_nonneg hzunit
  have hP :
      mediumCorrectionPolynomial (9 / 200) z ≤ 0 := by
    dsimp [mediumCorrectionPolynomial]
    have hz2 : z ^ 2 ≤ (269 / 1000 : ℝ) * z := by
      nlinarith [mul_nonneg hzunit.1
        (sub_nonneg.mpr hz.2)]
    have hz3 : 0 ≤ z ^ 3 :=
      mul_nonneg (sq_nonneg z) hzunit.1
    nlinarith [hz.2]
  have hq0 :
      0 ≤ tangentCoordSlopeMagnitudeLower (9 / 200) z := by
    unfold tangentCoordSlopeMagnitudeLower
    exact mul_nonneg (neg_nonneg.mpr hP) he0
  have hB0 : 0 ≤ tangentCoordBlueLower (9 / 200) z := by
    unfold tangentCoordBlueLower
    dsimp only
    exact mul_nonneg
      (mul_nonneg hzunit.1
        (inv_nonneg.mpr (by linarith [hzunit.1])))
      (by
        have hq2 := sq_nonneg
          (tangentCoordSlopeMagnitudeLower (9 / 200) z)
        nlinarith [hq0, hq2])
  have hblue := tangent_coord_blue_lower hzunit hP
  have hB1 : tangentCoordBlueLower (9 / 200) z < 1 :=
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
      (0 : ℝ) ≤ 269 / 1000)
    nlinarith
  have hX' := hX hB0 hB1 hM0 hM1
  linarith

end

end ForwardCoordRound1Bounds
end Arxiv2407_19026
