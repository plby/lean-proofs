import Arxiv.Arxiv2407_19026.TangentBackwardCoordBounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound1Back1ScaledSemantics

/-!
# First-round first backward coordinate bound

This file connects the two exact Bernstein certificates to the analytic
coordinate comparison on `[0.387, 0.6]`.
-/

namespace Arxiv2407_19026
namespace BackwardCoordRound1Back1Bounds

noncomputable section

open BackwardCoordRound1Back1Certificate

private def backwardCoordDenRound1Back1 (z : ℝ) : ℝ :=
  let t := r1Back1TReal z
  t * (1 + t) ^ 5 * (1 - backwardMuLower z)

lemma round1_back1_t_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5)) :
    0 < r1Back1TReal z ∧ r1Back1TReal z < 1 := by
  let u : ℝ := (1000 * z - 387) / 213
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have ht :
      r1Back1TReal z =
        (249306093407 / 250000000000 : ℝ) * (1 - u) ^ 4 +
          310744861940507 / 100000000000000 *
            u * (1 - u) ^ 3 +
          97008287575398177 / 25000000000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          2239691498340007821737 / 1000000000000000000000 *
            u ^ 3 * (1 - u) +
          495416422305329473874087 /
            1000000000000000000000000 * u ^ 4 := by
    dsimp [u, r1Back1TReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r1Back1Cs]
    ring
  have homt :
      1 - r1Back1TReal z =
        (693906593 / 250000000000 : ℝ) * (1 - u) ^ 4 +
          89255138059493 / 100000000000000 *
            u * (1 - u) ^ 3 +
          52991712424601823 / 25000000000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          1760308501659992178263 / 1000000000000000000000 *
            u ^ 3 * (1 - u) +
          504583577694670526125913 /
            1000000000000000000000000 * u ^ 4 := by
    dsimp [u, r1Back1TReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r1Back1Cs]
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

private lemma round1_back1_blue_fit_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5)) :
    0 < backwardBlueFitRound1Back1 z ∧
      backwardBlueFitRound1Back1 z < 1 := by
  let u : ℝ := (1000 * z - 387) / 213
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hB :
      backwardBlueFitRound1Back1 z =
        (297369725920712085404833 /
            1000000000000000000000000 : ℝ) * (1 - u) ^ 4 +
          6419354286331210298753 / 5000000000000000000000 *
            u * (1 - u) ^ 3 +
          51115154264139768243 / 25000000000000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          89525045540942149 / 62500000000000000 *
            u ^ 3 * (1 - u) +
          116741265523499 / 312500000000000 * u ^ 4 := by
    dsimp [u, backwardBlueFitRound1Back1]
    ring
  have homB :
      1 - backwardBlueFitRound1Back1 z =
        (702630274079287914595167 /
            1000000000000000000000000 : ℝ) * (1 - u) ^ 4 +
          13580645713668789701247 / 5000000000000000000000 *
            u * (1 - u) ^ 3 +
          98884845735860231757 / 25000000000000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          160474954459057851 / 62500000000000000 *
            u ^ 3 * (1 - u) +
          195758734476501 / 312500000000000 * u ^ 4 := by
    dsimp [u, backwardBlueFitRound1Back1]
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
    (hz : z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5)) :
    backwardBlueFitRound1Back1 z ≤
      backwardBlueRawLower (9 / 200) z := by
  let u : ℝ := (1000 * z - 387) / 213
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 49
    blueBernsteinCoeffs hu (by
      norm_num [blueBernsteinCoeffs, decimalNat]) (by
      norm_num [blueBernsteinCoeffs, decimalNat])
  have hpower := blue_power_eq_bernstein u
  have hzFromU : ((387 + 213 * u) / 1000 : ℝ) = z := by
    dsimp [u]
    ring
  rw [hzFromU] at hpower
  have hzplus : 0 < 1 + z := by nlinarith [hz.1]
  have hrat :
      backwardBlueRawLower (9 / 200) z -
          backwardBlueFitRound1Back1 z =
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
    (hz : z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5)) :
    0 <
      backwardBLogLower (2 / 25) (r1Back1TReal z) -
        backwardXLogUpper (backwardBlueFitRound1Back1 z) z := by
  let u : ℝ := (1000 * z - 387) / 213
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 66
    mainBernsteinCoeffs hu (by
      norm_num [mainBernsteinCoeffs, decimalNat]) (by
      norm_num [mainBernsteinCoeffs, decimalNat])
  have hpower := main_power_eq_bernstein u
  have hzFromU : ((387 + 213 * u) / 1000 : ℝ) = z := by
    dsimp [u]
    ring
  rw [hzFromU] at hpower
  obtain ⟨ht0, ht1⟩ := round1_back1_t_bounds hz
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
  have hden : 0 < backwardCoordDenRound1Back1 z := by
    dsimp [backwardCoordDenRound1Back1]
    positivity
  have hrat :
      backwardBLogLower (2 / 25) (r1Back1TReal z) -
          backwardXLogUpper (backwardBlueFitRound1Back1 z) z =
        (evalPower mainPowerCoeffs z / mainPowerScale) /
          backwardCoordDenRound1Back1 z := by
    simpa [backwardCoordDenRound1Back1] using
      coord_scaled_main_identity z ht0.ne'
        (by positivity : r1Back1TReal z + 1 ≠ 0)
        (sub_pos.mpr hM1).ne'
        (by
          simpa [backwardCoordDenRound1Back1] using hden.ne')
  rw [hrat, hpower]
  have hIdentityScale : (0 : ℝ) < mainIdentityScale := by
    norm_num [mainIdentityScale, decimalNat]
  have hPowerScale : (0 : ℝ) < mainPowerScale := by
    norm_num [mainPowerScale, decimalNat]
  positivity

/-- The first-round coordinate inequality on the first backward interval. -/
lemma tangent_backward_coord_round1_back1 :
    ∀ z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5),
      tangentXLog (9 / 200) z ≤
        tangentBLog (2 / 25) (r1Back1TReal z) := by
  intro z hz
  obtain ⟨ht0, ht1⟩ := round1_back1_t_bounds hz
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hfit := blue_fit_le_raw hz
  have hraw := backward_blue_raw_lower_le
    (β := (9 / 200 : ℝ)) (z := z) (by norm_num) hzunit
  obtain ⟨hB0, hB1⟩ := round1_back1_blue_fit_bounds hz
  have hX := tangent_xlog_le_backward
    (β := (9 / 200 : ℝ))
    (B := backwardBlueFitRound1Back1 z) (z := z)
    (by norm_num) hzunit hB0.le (hfit.trans hraw) hB1
  have hB := backward_blog_lower_le
    (β := (2 / 25 : ℝ)) (t := r1Back1TReal z)
    (by norm_num) ⟨ht0.le, ht1.le⟩ ht0
  have hstrict := backward_coord_lower_pos hz
  linarith

end

end BackwardCoordRound1Back1Bounds
end Arxiv2407_19026
