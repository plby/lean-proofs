import Arxiv.Arxiv2407_19026.TangentBackwardCoordBounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound3Back1ScaledSemantics

/-!
# Third-round first backward coordinate bound

This file connects the two exact Bernstein certificates to the analytic
coordinate comparison on `[0.375, 0.6]`.
-/

namespace Arxiv2407_19026
namespace BackwardCoordRound3Back1Bounds

noncomputable section

open BackwardCoordRound3Back1Certificate

private def backwardCoordDenRound3Back1 (z : ℝ) : ℝ :=
  let t := r3Back1TReal z
  t * (1 + t) ^ 7 * (1 - backwardMuLower z)

lemma round3_back1_t_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5)) :
    0 < r3Back1TReal z ∧ r3Back1TReal z < 1 := by
  let u : ℝ := (40 * z - 15) / 9
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have ht :
      r3Back1TReal z =
        (9960451727 / 10000000000 : ℝ) * (1 - u) ^ 4 +
          119680288639739 / 40000000000000 *
            u * (1 - u) ^ 3 +
          5951951679122229 / 1600000000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          106552601641729 / 50000000000000 *
            u ^ 3 * (1 - u) +
          1203482098196445539 /
            2560000000000000000 * u ^ 4 := by
    dsimp [u, r3Back1TReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r3Back1Cs]
    ring
  have homt :
      1 - r3Back1TReal z =
        (39548273 / 10000000000 : ℝ) * (1 - u) ^ 4 +
          40319711360261 / 40000000000000 *
            u * (1 - u) ^ 3 +
          3648048320877771 / 1600000000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          93447398358271 / 50000000000000 *
            u ^ 3 * (1 - u) +
          1356517901803554461 /
            2560000000000000000 * u ^ 4 := by
    dsimp [u, r3Back1TReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r3Back1Cs]
    ring
  constructor
  · rw [ht]
    by_cases hzero : u = 0
    · simp [hzero]
    · have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hzero)
      positivity
  · rw [← sub_pos, homt]
    by_cases hzero : u = 0
    · simp [hzero]
    · have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hzero)
      positivity

private lemma round3_back1_blue_fit_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5)) :
    0 < backwardBlueFitRound3Back1 z ∧
      backwardBlueFitRound3Back1 z < 1 := by
  let u : ℝ := (40 * z - 15) / 9
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hB :
      backwardBlueFitRound3Back1 z =
        (1203472051763309 /
            4096000000000000 : ℝ) * (1 - u) ^ 4 +
          3273822440962481 / 2560000000000000 *
            u * (1 - u) ^ 3 +
          3274894241189301 / 1600000000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          57554245011467 / 40000000000000 *
            u ^ 3 * (1 - u) +
          29387762133817 / 78125000000000 * u ^ 4 := by
    dsimp [u, backwardBlueFitRound3Back1]
    ring
  have homB :
      1 - backwardBlueFitRound3Back1 z =
        (2892527948236691 /
            4096000000000000 : ℝ) * (1 - u) ^ 4 +
          6966177559037519 / 2560000000000000 *
            u * (1 - u) ^ 3 +
          6325105758810699 / 1600000000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          102445754988533 / 40000000000000 *
            u ^ 3 * (1 - u) +
          48737237866183 / 78125000000000 * u ^ 4 := by
    dsimp [u, backwardBlueFitRound3Back1]
    ring
  constructor
  · rw [hB]
    by_cases hzero : u = 0
    · simp [hzero]
    · have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hzero)
      positivity
  · rw [← sub_pos, homB]
    by_cases hzero : u = 0
    · simp [hzero]
    · have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hzero)
      positivity

private lemma blue_fit_le_raw {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5)) :
    backwardBlueFitRound3Back1 z ≤
      backwardBlueRawLower (3 / 100) z := by
  let u : ℝ := (40 * z - 15) / 9
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 49
    blueBernsteinCoeffs hu (by
      norm_num [blueBernsteinCoeffs, decimalNat]) (by
      norm_num [blueBernsteinCoeffs, decimalNat])
  have hpower := blue_power_eq_bernstein u
  have hzFromU : ((15 + 9 * u) / 40 : ℝ) = z := by
    dsimp [u]
    ring
  rw [hzFromU] at hpower
  have hzplus : 0 < 1 + z := by nlinarith [hz.1]
  have hrat :
      backwardBlueRawLower (3 / 100) z -
          backwardBlueFitRound3Back1 z =
        (evalPower bluePowerCoeffs z / bluePowerScale) /
          (1 + z) := by
    exact coord_scaled_blue_identity z hzplus.ne'
  rw [← sub_nonneg, hrat, hpower]
  have hIdentityScale : (0 : ℝ) < blueIdentityScale := by
    norm_num [blueIdentityScale, decimalNat]
  have hPowerScale : (0 : ℝ) < bluePowerScale := by
    norm_num [bluePowerScale, decimalNat]
  positivity

private lemma backward_coord_lower_pos {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5)) :
    0 <
      backwardBLogLowerFour (33 / 1000) (r3Back1TReal z) -
        backwardXLogUpper (backwardBlueFitRound3Back1 z) z := by
  let u : ℝ := (40 * z - 15) / 9
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 74
    mainBernsteinCoeffs hu (by
      norm_num [mainBernsteinCoeffs, decimalNat]) (by
      norm_num [mainBernsteinCoeffs, decimalNat])
  have hpower := main_power_eq_bernstein u
  have hzFromU : ((15 + 9 * u) / 40 : ℝ) = z := by
    dsimp [u]
    ring
  rw [hzFromU] at hpower
  obtain ⟨ht0, ht1⟩ := round3_back1_t_bounds hz
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have happrox := backward_exp_approx5 hzunit
  have hM :
      backwardMuLower z ≤ optimizationM z := by
    unfold backwardMuLower backwardExpLower5 optimizationM
    exact mul_le_mul_of_nonneg_left
      (by linarith [abs_le.mp happrox]) hzunit.1
  have hM1 : backwardMuLower z < 1 :=
    hM.trans_lt
      (optimizationM_lt_one_of_Icc hzunit.1 hzunit.2)
  have hden : 0 < backwardCoordDenRound3Back1 z := by
    dsimp [backwardCoordDenRound3Back1]
    positivity
  have hrat :
      backwardBLogLowerFour (33 / 1000) (r3Back1TReal z) -
          backwardXLogUpper (backwardBlueFitRound3Back1 z) z =
        (evalPower mainPowerCoeffs z / mainPowerScale) /
          backwardCoordDenRound3Back1 z := by
    simpa [backwardCoordDenRound3Back1] using
      coord_scaled_main_identity z ht0.ne'
        (by positivity : r3Back1TReal z + 1 ≠ 0)
        (sub_pos.mpr hM1).ne'
        (by
          simpa [backwardCoordDenRound3Back1] using hden.ne')
  rw [hrat, hpower]
  have hIdentityScale : (0 : ℝ) < mainIdentityScale := by
    norm_num [mainIdentityScale, decimalNat]
  have hPowerScale : (0 : ℝ) < mainPowerScale := by
    norm_num [mainPowerScale, decimalNat]
  positivity

/-- The third-round coordinate inequality on the first backward interval. -/
lemma tangent_backward_coord_round3_back1 :
    ∀ z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5),
      tangentXLog (3 / 100) z ≤
        tangentBLog (33 / 1000) (r3Back1TReal z) := by
  intro z hz
  obtain ⟨ht0, ht1⟩ := round3_back1_t_bounds hz
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hfit := blue_fit_le_raw hz
  have hraw := backward_blue_raw_lower_le
    (β := (3 / 100 : ℝ)) (z := z) (by norm_num) hzunit
  obtain ⟨hB0, hB1⟩ := round3_back1_blue_fit_bounds hz
  have hX := tangent_xlog_le_backward
    (β := (3 / 100 : ℝ))
    (B := backwardBlueFitRound3Back1 z) (z := z)
    (by norm_num) hzunit hB0.le (hfit.trans hraw) hB1
  have hB := backward_blog_lower_four_le
    (β := (33 / 1000 : ℝ)) (t := r3Back1TReal z)
    (by norm_num) ⟨ht0.le, ht1.le⟩ ht0
  have hstrict := backward_coord_lower_pos hz
  linarith

end

end BackwardCoordRound3Back1Bounds
end Arxiv2407_19026
