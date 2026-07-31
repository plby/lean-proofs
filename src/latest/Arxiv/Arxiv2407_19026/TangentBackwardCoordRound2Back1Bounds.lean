import Arxiv.Arxiv2407_19026.TangentBackwardCoordBounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound2Back1Certificate

/-!
# Second-round first backward coordinate bound

This file connects the two exact Bernstein certificates to the analytic
coordinate comparison on `[0.378, 0.6]`.
-/

namespace Arxiv2407_19026
namespace BackwardCoordRound2Back1Bounds

noncomputable section

open BackwardCoordRound2Back1Certificate

def backwardBlueFitRound2Back1 (z : ℝ) : ℝ :=
  1950931 / 195312500 +
    58478641629 / 50000000000 * z -
    732508917503 / 500000000000 * z ^ 2 +
    137135452249 / 125000000000 * z ^ 3 -
    352251748243 / 1000000000000 * z ^ 4 -
    74489 / 125000000000

private def backwardCoordDenRound2Back1 (z : ℝ) : ℝ :=
  let t := r2Back1TReal z
  t * (1 + t) ^ 7 * (1 - backwardMuLower z)

private lemma evalPower_eq_bernstein_of_identity
    (degree scale : ℕ) (coefficients : List ℤ)
    (bernsteinCoefficients : List ℕ)
    (hscale : scale ≠ 0)
    (hlength : coefficients.length = degree + 1)
    (hidentity :
      ((scale : ℤ) : Polynomial ℤ) * homogenized coefficients =
        (500 ^ degree : Polynomial ℤ) *
          BackwardCoordRound2Back1Certificate.bernsteinPolynomial
            degree bernsteinCoefficients)
    (u : ℝ) :
    evalPower coefficients ((189 + 111 * u) / 500) =
      (∑ i ∈ Finset.range (degree + 1),
        (bernsteinCoefficients.getD i 0 : ℝ) *
          u ^ i * (1 - u) ^ (degree - i)) / scale := by
  have hBernstein :
      Polynomial.eval₂ (Int.castRingHom ℝ) u
          (BackwardCoordRound2Back1Certificate.bernsteinPolynomial
            degree bernsteinCoefficients) =
        ∑ i ∈ Finset.range (degree + 1),
          (bernsteinCoefficients.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (degree - i) := by
    dsimp [BackwardCoordRound2Back1Certificate.bernsteinPolynomial]
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
        500 ^ degree *
          evalPower coefficients ((189 + 111 * u) / 500) := by
    apply mul_right_cancel₀ (by norm_num : (500 : ℝ) ≠ 0)
    calc
      _ = 500 ^ (degree + 1) *
          evalPower coefficients ((189 + 111 * u) / 500) := hhom
      _ = _ := by ring
  have hpoly := congrArg
    (Polynomial.eval₂ (Int.castRingHom ℝ) u) hidentity
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_ofNat] at hpoly
  rw [hBernstein, hhom'] at hpoly
  rw [eq_div_iff (by exact_mod_cast hscale)]
  apply mul_left_cancel₀ (by positivity : (500 : ℝ) ^ degree ≠ 0)
  calc
    _ = (scale : ℝ) *
        (500 ^ degree *
          evalPower coefficients ((189 + 111 * u) / 500)) := by
      ring
    _ = _ := by simpa using hpoly

lemma round2_back1_t_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (189 / 500 : ℝ) (3 / 5)) :
    0 < r2Back1TReal z ∧ r2Back1TReal z < 1 := by
  let u : ℝ := (500 * z - 189) / 111
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have ht :
      r2Back1TReal z =
        (99600189721 / 100000000000 : ℝ) * (1 - u) ^ 4 +
          188790351601483 / 62500000000000 *
            u * (1 - u) ^ 3 +
          939322099090632741 / 250000000000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          53919419294645233711 / 25000000000000000000 *
            u ^ 3 * (1 - u) +
          7438004294839916618011 /
            15625000000000000000000 * u ^ 4 := by
    dsimp [u, r2Back1TReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r2Back1Cs]
    ring
  have homt :
      1 - r2Back1TReal z =
        (399810279 / 100000000000 : ℝ) * (1 - u) ^ 4 +
          61209648398517 / 62500000000000 *
            u * (1 - u) ^ 3 +
          560677900909367259 / 250000000000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          46080580705354766289 / 25000000000000000000 *
            u ^ 3 * (1 - u) +
          8186995705160083381989 /
            15625000000000000000000 * u ^ 4 := by
    dsimp [u, r2Back1TReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r2Back1Cs]
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

private lemma round2_back1_blue_fit_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (189 / 500 : ℝ) (3 / 5)) :
    0 < backwardBlueFitRound2Back1 z ∧
      backwardBlueFitRound2Back1 z < 1 := by
  let u : ℝ := (500 * z - 189) / 111
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hB :
      backwardBlueFitRound2Back1 z =
        (18426326982186226824637 /
            62500000000000000000000 : ℝ) * (1 - u) ^ 4 +
          200087213180230832209 / 156250000000000000000 *
            u * (1 - u) ^ 3 +
          1599199933908296541 / 781250000000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          22464660252521041 / 15625000000000000 *
            u ^ 3 * (1 - u) +
          234777302917387 / 625000000000000 * u ^ 4 := by
    dsimp [u, backwardBlueFitRound2Back1]
    ring
  have homB :
      1 - backwardBlueFitRound2Back1 z =
        (44073673017813773175363 /
            62500000000000000000000 : ℝ) * (1 - u) ^ 4 +
          424912786819769167791 / 156250000000000000000 *
            u * (1 - u) ^ 3 +
          3088300066091703459 / 781250000000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          40035339747478959 / 15625000000000000 *
            u ^ 3 * (1 - u) +
          390222697082613 / 625000000000000 * u ^ 4 := by
    dsimp [u, backwardBlueFitRound2Back1]
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
    (hz : z ∈ Set.Icc (189 / 500 : ℝ) (3 / 5)) :
    backwardBlueFitRound2Back1 z ≤
      backwardBlueRawLower (33 / 1000) z := by
  let u : ℝ := (500 * z - 189) / 111
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
  have hzFromU : ((189 + 111 * u) / 500 : ℝ) = z := by
    dsimp [u]
    ring
  rw [hzFromU] at hpower
  have hzplus : 0 < 1 + z := by nlinarith [hz.1]
  have hrat :
      backwardBlueRawLower (33 / 1000) z -
          backwardBlueFitRound2Back1 z =
        (evalPower bluePowerCoeffs z / bluePowerScale) /
          (1 + z) := by
    apply (eq_div_iff hzplus.ne').2
    dsimp [backwardBlueRawLower, backwardExpQLower,
      backwardQLower, backwardBlueFitRound2Back1,
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
-- Expanding the degree-74 final coordinate certificate exceeds the default budget.
set_option maxRecDepth 30000 in
-- The exact rational identity also needs additional simplifier recursion.
private lemma backward_coord_lower_pos {z : ℝ}
    (hz : z ∈ Set.Icc (189 / 500 : ℝ) (3 / 5)) :
    0 <
      backwardBLogLowerFour (9 / 200) (r2Back1TReal z) -
        backwardXLogUpper (backwardBlueFitRound2Back1 z) z := by
  let u : ℝ := (500 * z - 189) / 111
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 74
    mainBernsteinCoeffs hu (by
      norm_num [mainBernsteinCoeffs, decimalNat]) (by
      norm_num [mainBernsteinCoeffs, decimalNat])
  have hpower := evalPower_eq_bernstein_of_identity
    74 mainIdentityScale mainPowerCoeffs mainBernsteinCoeffs
    (by norm_num [mainIdentityScale, decimalNat])
    (by norm_num [mainPowerCoeffs]) main_polynomial_identity u
  have hzFromU : ((189 + 111 * u) / 500 : ℝ) = z := by
    dsimp [u]
    ring
  rw [hzFromU] at hpower
  obtain ⟨ht0, ht1⟩ := round2_back1_t_bounds hz
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
  have hden : 0 < backwardCoordDenRound2Back1 z := by
    dsimp [backwardCoordDenRound2Back1]
    positivity
  have hrat :
      backwardBLogLowerFour (9 / 200) (r2Back1TReal z) -
          backwardXLogUpper (backwardBlueFitRound2Back1 z) z =
        (evalPower mainPowerCoeffs z / mainPowerScale) /
          backwardCoordDenRound2Back1 z := by
    apply (eq_div_iff hden.ne').2
    unfold backwardBLogLowerFour backwardXLogUpper
      backwardCoordDenRound2Back1
    dsimp only
    rw [backward_log_lower_below_four_closed
      ht0.ne' (by positivity : r2Back1TReal z + 1 ≠ 0)]
    unfold backwardLogLowerFourClosed tangentCoordLogUpper
      backwardLogUpperBelowFive
    field_simp [ht0.ne', (sub_pos.mpr hM1).ne',
      (by positivity : r2Back1TReal z + 1 ≠ 0)]
    unfold backwardMuLower
      backwardExpLower5 backwardExpTaylor5 backwardExpError6
      backwardBlueFitRound2Back1 mediumCorrectionPolynomial
    norm_num [Finset.sum_range_succ, Nat.factorial]
    dsimp [r2Back1TReal, tangentLocalPoly, tangentRatHorner,
      TangentAffine.r2Back1Cs, evalPower, mainPowerCoeffs,
      mainPowerScale, decimalNat]
    ring
  rw [hrat, hpower]
  have hIdentityScale : (0 : ℝ) < mainIdentityScale := by
    norm_num [mainIdentityScale, decimalNat]
  have hPowerScale : (0 : ℝ) < mainPowerScale := by
    norm_num [mainPowerScale, decimalNat]
  positivity

/-- The second-round coordinate inequality on the first backward interval. -/
lemma tangent_backward_coord_round2_back1 :
    ∀ z ∈ Set.Icc (189 / 500 : ℝ) (3 / 5),
      tangentXLog (33 / 1000) z ≤
        tangentBLog (9 / 200) (r2Back1TReal z) := by
  intro z hz
  obtain ⟨ht0, ht1⟩ := round2_back1_t_bounds hz
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hfit := blue_fit_le_raw hz
  have hraw := backward_blue_raw_lower_le
    (β := (33 / 1000 : ℝ)) (z := z) (by norm_num) hzunit
  obtain ⟨hB0, hB1⟩ := round2_back1_blue_fit_bounds hz
  have hX := tangent_xlog_le_backward
    (β := (33 / 1000 : ℝ))
    (B := backwardBlueFitRound2Back1 z) (z := z)
    (by norm_num) hzunit hB0.le (hfit.trans hraw) hB1
  have hB := backward_blog_lower_four_le
    (β := (9 / 200 : ℝ)) (t := r2Back1TReal z)
    (by norm_num) ⟨ht0.le, ht1.le⟩ ht0
  have hstrict := backward_coord_lower_pos hz
  linarith

end

end BackwardCoordRound2Back1Bounds
end Arxiv2407_19026
