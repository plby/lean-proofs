import Arxiv.Arxiv2407_19026.TangentBackwardCoordBounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound1Back1Certificate

/-!
# First-round first backward coordinate bound

This file connects the two exact Bernstein certificates to the analytic
coordinate comparison on `[0.387, 0.6]`.
-/

namespace Arxiv2407_19026
namespace BackwardCoordRound1Back1Bounds

noncomputable section

open BackwardCoordRound1Back1Certificate

def backwardBlueFitRound1Back1 (z : ℝ) : ℝ :=
  10836411657 / 1000000000000 +
    1160876492237 / 1000000000000 * z -
    728801313177 / 500000000000 * z ^ 2 +
    1094952949203 / 1000000000000 * z ^ 3 -
    351563684247 / 1000000000000 * z ^ 4 -
    247693 / 500000000000

private def backwardCoordDenRound1Back1 (z : ℝ) : ℝ :=
  let t := r1Back1TReal z
  t * (1 + t) ^ 5 * (1 - backwardMuLower z)

private lemma evalPower_eq_bernstein_of_identity
    (degree scale : ℕ) (coefficients : List ℤ)
    (bernsteinCoefficients : List ℕ)
    (hscale : scale ≠ 0)
    (hlength : coefficients.length = degree + 1)
    (hidentity :
      ((scale : ℤ) : Polynomial ℤ) * homogenized coefficients =
        (1000 ^ degree : Polynomial ℤ) *
          BackwardCoordRound1Back1Certificate.bernsteinPolynomial
            degree bernsteinCoefficients)
    (u : ℝ) :
    evalPower coefficients ((387 + 213 * u) / 1000) =
      (∑ i ∈ Finset.range (degree + 1),
        (bernsteinCoefficients.getD i 0 : ℝ) *
          u ^ i * (1 - u) ^ (degree - i)) / scale := by
  have hBernstein :
      Polynomial.eval₂ (Int.castRingHom ℝ) u
          (BackwardCoordRound1Back1Certificate.bernsteinPolynomial
            degree bernsteinCoefficients) =
        ∑ i ∈ Finset.range (degree + 1),
          (bernsteinCoefficients.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (degree - i) := by
    dsimp [BackwardCoordRound1Back1Certificate.bernsteinPolynomial]
    change
      (Polynomial.eval₂RingHom (Int.castRingHom ℝ) u)
          (∑ i ∈ Finset.range (degree + 1),
            (bernsteinCoefficients.getD i 0 :
                Polynomial ℤ) *
              Polynomial.X ^ i *
                ((1 : Polynomial ℤ) - Polynomial.X) ^
                  (degree - i)) =
        _
    simp [Polynomial.eval₂_pow]
  have hhom := eval₂_homogenized coefficients u
  rw [hlength] at hhom
  have hhom' :
      Polynomial.eval₂ (Int.castRingHom ℝ) u
          (homogenized coefficients) =
        1000 ^ degree *
          evalPower coefficients ((387 + 213 * u) / 1000) := by
    apply mul_right_cancel₀ (by norm_num : (1000 : ℝ) ≠ 0)
    calc
      _ = 1000 ^ (degree + 1) *
          evalPower coefficients ((387 + 213 * u) / 1000) := hhom
      _ = _ := by ring
  have hpoly := congrArg
    (Polynomial.eval₂ (Int.castRingHom ℝ) u) hidentity
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_ofNat] at hpoly
  rw [hBernstein, hhom'] at hpoly
  rw [eq_div_iff (by exact_mod_cast hscale)]
  apply mul_left_cancel₀ (by positivity : (1000 : ℝ) ^ degree ≠ 0)
  calc
    _ = (scale : ℝ) *
        (1000 ^ degree *
          evalPower coefficients ((387 + 213 * u) / 1000)) := by
      ring
    _ = _ := by simpa using hpoly

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

set_option maxHeartbeats 0 in
-- Expanding the degree-49 blue certificate exceeds the default heartbeat budget.
set_option maxRecDepth 30000 in
-- The exact rational identity also needs additional simplifier recursion.
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
  have hpower := evalPower_eq_bernstein_of_identity
    49 blueIdentityScale bluePowerCoeffs blueBernsteinCoeffs
    (by norm_num [blueIdentityScale, decimalNat])
    (by norm_num [bluePowerCoeffs]) blue_polynomial_identity u
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
    apply (eq_div_iff hzplus.ne').2
    dsimp [backwardBlueRawLower, backwardExpQLower,
      backwardQLower, backwardBlueFitRound1Back1,
      mediumCorrectionPolynomial]
    norm_num [KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Finset.sum_range_succ,
      Nat.factorial]
    dsimp [evalPower, bluePowerCoeffs, bluePowerScale,
      decimalNat]
    field_simp
    ring
  rw [← sub_nonneg, hrat, hpower]
  have hIdentityScale : (0 : ℝ) < blueIdentityScale := by
    norm_num [blueIdentityScale, decimalNat]
  have hPowerScale : (0 : ℝ) < bluePowerScale := by
    norm_num [bluePowerScale, decimalNat]
  positivity

set_option maxHeartbeats 0 in
-- Expanding the degree-66 final coordinate certificate exceeds the default budget.
set_option maxRecDepth 30000 in
-- The exact rational identity also needs additional simplifier recursion.
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
  have hpower := evalPower_eq_bernstein_of_identity
    66 mainIdentityScale mainPowerCoeffs mainBernsteinCoeffs
    (by norm_num [mainIdentityScale, decimalNat])
    (by norm_num [mainPowerCoeffs]) main_polynomial_identity u
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
    apply (eq_div_iff hden.ne').2
    unfold backwardBLogLower backwardXLogUpper
      backwardCoordDenRound1Back1
    dsimp only
    rw [backward_log_lower_below_three_closed
      ht0.ne' (by positivity : r1Back1TReal z + 1 ≠ 0)]
    unfold backwardLogLowerThreeClosed tangentCoordLogUpper
      backwardLogUpperBelowFive
    field_simp [ht0.ne', (sub_pos.mpr hM1).ne',
      (by positivity : r1Back1TReal z + 1 ≠ 0)]
    unfold backwardMuLower
      backwardExpLower5 backwardExpTaylor5 backwardExpError6
      backwardBlueFitRound1Back1 mediumCorrectionPolynomial
    norm_num [Finset.sum_range_succ, Nat.factorial]
    dsimp [r1Back1TReal, tangentLocalPoly, tangentRatHorner,
      TangentAffine.r1Back1Cs, evalPower, mainPowerCoeffs,
      mainPowerScale, decimalNat]
    ring
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
