import Arxiv.Arxiv2407_19026.TangentBackwardCoordBounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound1Back2Certificate

/-!
# First-round second backward coordinate bound

This file connects the exact Bernstein certificates to the analytic
coordinate comparison on `[0.6, 1]`.
-/

namespace Arxiv2407_19026
namespace BackwardCoordRound1Back2Bounds

noncomputable section

open BackwardCoordRound1Back2Certificate

def backwardBlueFitRound1Back2 (z : ℝ) : ℝ :=
  2878037309 / 62500000000 +
    939477058859 / 1000000000000 * z -
    464704506967 / 500000000000 * z ^ 2 +
    527887379907 / 1000000000000 * z ^ 3 -
    24065962519 / 200000000000 * z ^ 4 -
    1776741 / 500000000000

def backwardBLogFitRound1Back2 (z : ℝ) : ℝ :=
  3373214585107 / 1000000000000 -
    39561727347647 / 1000000000000 * z +
    84687045889699 / 500000000000 * z ^ 2 -
    414602883456471 / 1000000000000 * z ^ 3 +
    76219166258741 / 125000000000 * z ^ 4 -
    550564850968423 / 1000000000000 * z ^ 5 +
    37411202194051 / 125000000000 * z ^ 6 -
    4510480483343 / 50000000000 * z ^ 7 +
    11706158587431 / 1000000000000 * z ^ 8 -
    44539 / 500000000000

private def backwardBLogDenRound1Back2 (z : ℝ) : ℝ :=
  let t := r1Back2TReal z
  t * (1 + 2 * t) ^ 5

private lemma evalPower_eq_bernstein_of_identity
    (denominator degree scale : ℕ) (left width : ℤ)
    (coefficients : List ℤ)
    (bernsteinCoefficients : List ℕ)
    (hdenominator : denominator ≠ 0)
    (hscale : scale ≠ 0)
    (hlength : coefficients.length = degree + 1)
    (hidentity :
      ((scale : ℤ) : Polynomial ℤ) *
          homogenizedAffine denominator left width coefficients =
        (denominator ^ degree : Polynomial ℤ) *
          BackwardCoordRound1Back2Certificate.bernsteinPolynomial
            degree bernsteinCoefficients)
    (u : ℝ) :
    evalPower coefficients
        (((left : ℝ) + (width : ℝ) * u) / denominator) =
      (∑ i ∈ Finset.range (degree + 1),
        (bernsteinCoefficients.getD i 0 : ℝ) *
          u ^ i * (1 - u) ^ (degree - i)) / scale := by
  have hBernstein :
      Polynomial.eval₂ (Int.castRingHom ℝ) u
          (BackwardCoordRound1Back2Certificate.bernsteinPolynomial
            degree bernsteinCoefficients) =
        ∑ i ∈ Finset.range (degree + 1),
          (bernsteinCoefficients.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (degree - i) := by
    dsimp [BackwardCoordRound1Back2Certificate.bernsteinPolynomial]
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
  have hhom := eval₂_homogenizedAffine
    denominator left width coefficients u hdenominator
  rw [hlength] at hhom
  have hhom' :
      Polynomial.eval₂ (Int.castRingHom ℝ) u
          (homogenizedAffine denominator left width coefficients) =
        denominator ^ degree *
          evalPower coefficients
            (((left : ℝ) + (width : ℝ) * u) / denominator) := by
    apply mul_right_cancel₀
      (by exact_mod_cast hdenominator : (denominator : ℝ) ≠ 0)
    calc
      _ = denominator ^ (degree + 1) *
          evalPower coefficients
            (((left : ℝ) + (width : ℝ) * u) / denominator) :=
        hhom
      _ = _ := by ring
  have hpoly := congrArg
    (Polynomial.eval₂ (Int.castRingHom ℝ) u) hidentity
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow] at hpoly
  rw [hBernstein, hhom'] at hpoly
  rw [eq_div_iff (by exact_mod_cast hscale)]
  apply mul_left_cancel₀
    (by positivity : (denominator : ℝ) ^ degree ≠ 0)
  calc
    _ = (scale : ℝ) *
        (denominator ^ degree *
          evalPower coefficients
            (((left : ℝ) + (width : ℝ) * u) / denominator)) := by
      ring
    _ = _ := by simpa using hpoly

private lemma positive_of_certificate
    (denominator degree identityScale powerScale : ℕ)
    (left width : ℤ) (powerCoefficients : List ℤ)
    (bernsteinCoefficients : List ℕ)
    (hdenominator : denominator ≠ 0)
    (hidentityScale : identityScale ≠ 0)
    (hpowerScale : powerScale ≠ 0)
    (hlength : powerCoefficients.length = degree + 1)
    (hfirst : 0 < bernsteinCoefficients.getD 0 0)
    (hlast : 0 < bernsteinCoefficients.getD degree 0)
    (hidentity :
      ((identityScale : ℤ) : Polynomial ℤ) *
          homogenizedAffine denominator left width powerCoefficients =
        (denominator ^ degree : Polynomial ℤ) *
          BackwardCoordRound1Back2Certificate.bernsteinPolynomial
            degree bernsteinCoefficients)
    (u point value semanticDenominator : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hpoint :
      ((left : ℝ) + (width : ℝ) * u) / denominator = point)
    (hsemanticDenominator : 0 < semanticDenominator)
    (hvalue :
      value =
        (evalPower powerCoefficients point / powerScale) /
          semanticDenominator) :
    0 < value := by
  have hsum := bernstein_sum_pos_of_ends degree
    bernsteinCoefficients hu hfirst hlast
  have hpower := evalPower_eq_bernstein_of_identity
    denominator degree identityScale left width powerCoefficients
    bernsteinCoefficients hdenominator hidentityScale hlength
    hidentity u
  rw [hpoint] at hpower
  rw [hvalue, hpower]
  have hIdentityScale : (0 : ℝ) < identityScale := by
    exact_mod_cast Nat.pos_of_ne_zero hidentityScale
  have hPowerScale : (0 : ℝ) < powerScale := by
    exact_mod_cast Nat.pos_of_ne_zero hpowerScale
  positivity

lemma round1_back2_t_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 5 : ℝ) 1) :
    0 < r1Back2TReal z ∧ r1Back2TReal z ≤ 1 / 2 := by
  let u : ℝ := (5 * z - 3) / 2
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have ht :
      r1Back2TReal z =
        (98683284461 / 200000000000 : ℝ) * (1 - u) ^ 4 +
          3748922905371 / 2500000000000 *
            u * (1 - u) ^ 3 +
          12416453065507 / 6250000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          73561236583161 / 62500000000000 *
            u ^ 3 * (1 - u) +
          6827928060531 / 25000000000000 * u ^ 4 := by
    dsimp [u, r1Back2TReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r1Back2Cs]
    ring
  have hhalft :
      1 / 2 - r1Back2TReal z =
        (1316715539 / 200000000000 : ℝ) * (1 - u) ^ 4 +
          1251077094629 / 2500000000000 *
            u * (1 - u) ^ 3 +
          6333546934493 / 6250000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          51438763416839 / 62500000000000 *
            u ^ 3 * (1 - u) +
          5672071939469 / 25000000000000 * u ^ 4 := by
    dsimp [u, r1Back2TReal, tangentLocalPoly,
      tangentRatHorner, TangentAffine.r1Back2Cs]
    ring
  constructor
  · rw [ht]
    by_cases hzero : u = 0
    · simp [hzero]
    · have hupos : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hzero)
      positivity
  · rw [← sub_nonneg, hhalft]
    positivity

private lemma round1_back2_blue_fit_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 5 : ℝ) 1) :
    0 < backwardBlueFitRound1Back2 z ∧
      backwardBlueFitRound1Back2 z < 1 := by
  let u : ℝ := (5 * z - 3) / 2
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hB :
      backwardBlueFitRound1Back2 z =
        (9339324102719 / 25000000000000 : ℝ) * (1 - u) ^ 4 +
          50325866193041 / 31250000000000 *
            u * (1 - u) ^ 3 +
          31894818872879 / 12500000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          2226852318329 / 1250000000000 *
            u ^ 3 * (1 - u) +
          463670655699 / 1000000000000 * u ^ 4 := by
    dsimp [u, backwardBlueFitRound1Back2]
    ring
  have homB :
      1 - backwardBlueFitRound1Back2 z =
        (15660675897281 / 25000000000000 : ℝ) * (1 - u) ^ 4 +
          74674133806959 / 31250000000000 *
            u * (1 - u) ^ 3 +
          43105181127121 / 12500000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          2773147681671 / 1250000000000 *
            u ^ 3 * (1 - u) +
          536329344301 / 1000000000000 * u ^ 4 := by
    dsimp [u, backwardBlueFitRound1Back2]
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
    (hz : z ∈ Set.Icc (3 / 5 : ℝ) 1) :
    backwardBlueFitRound1Back2 z ≤
      backwardBlueRawLower (9 / 200) z := by
  let u : ℝ := (5 * z - 3) / 2
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hpoint : ((3 + 2 * u) / 5 : ℝ) = z := by
    dsimp [u]
    ring
  have hzplus : 0 < 1 + z := by nlinarith [hz.1]
  have hrat :
      backwardBlueRawLower (9 / 200) z -
          backwardBlueFitRound1Back2 z =
        (evalPower bluePowerCoeffs z / bluePowerScale) /
          (1 + z) := by
    apply (eq_div_iff hzplus.ne').2
    dsimp [backwardBlueRawLower, backwardExpQLower,
      backwardQLower, backwardBlueFitRound1Back2,
      mediumCorrectionPolynomial]
    norm_num [KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Finset.sum_range_succ,
      Nat.factorial]
    dsimp [evalPower, bluePowerCoeffs, bluePowerScale,
      decimalNat]
    field_simp
    ring
  rw [← sub_nonneg]
  exact (positive_of_certificate
    5 49 blueIdentityScale bluePowerScale 3 2
    bluePowerCoeffs blueBernsteinCoeffs
    (by norm_num) (by
      norm_num [blueIdentityScale, decimalNat]) (by
      norm_num [bluePowerScale, decimalNat])
    (by norm_num [bluePowerCoeffs])
    (by norm_num [blueBernsteinCoeffs, decimalNat])
    (by norm_num [blueBernsteinCoeffs, decimalNat])
    blue_polynomial_identity u z
    (backwardBlueRawLower (9 / 200) z -
      backwardBlueFitRound1Back2 z)
    (1 + z) hu hpoint hzplus hrat).le

set_option maxHeartbeats 0 in
-- Expanding the degree-56 B-log certificate exceeds the default heartbeat budget.
set_option maxRecDepth 30000 in
-- The exact rational identity also needs additional simplifier recursion.
private lemma blog_fit_lt_lower {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 5 : ℝ) 1) :
    backwardBLogFitRound1Back2 z <
      backwardBLogLowerScaledThree (2 / 25) (r1Back2TReal z) := by
  let u : ℝ := (5 * z - 3) / 2
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hpoint : ((3 + 2 * u) / 5 : ℝ) = z := by
    dsimp [u]
    ring
  obtain ⟨ht0, htHalf⟩ := round1_back2_t_bounds hz
  have hden : 0 < backwardBLogDenRound1Back2 z := by
    dsimp [backwardBLogDenRound1Back2]
    positivity
  have hrat :
      backwardBLogLowerScaledThree (2 / 25) (r1Back2TReal z) -
          backwardBLogFitRound1Back2 z =
        (evalPower blogPowerCoeffs z / blogPowerScale) /
          backwardBLogDenRound1Back2 z := by
    apply (eq_div_iff hden.ne').2
    unfold backwardBLogLowerScaledThree
      backwardLogLowerScaledThree backwardBLogDenRound1Back2
    dsimp only
    rw [backward_log_lower_below_three_closed
      (by positivity : 2 * r1Back2TReal z ≠ 0)
      (by positivity : 2 * r1Back2TReal z + 1 ≠ 0)]
    unfold backwardLogLowerThreeClosed tangentCoordLogUpper
    field_simp [ht0.ne',
      (by positivity : 2 * r1Back2TReal z + 1 ≠ 0)]
    unfold backwardExpTaylor5 backwardExpError6
      backwardBLogFitRound1Back2 mediumCorrectionPolynomial
    norm_num [Finset.sum_range_succ, Nat.factorial]
    dsimp [r1Back2TReal, tangentLocalPoly, tangentRatHorner,
      TangentAffine.r1Back2Cs, evalPower, blogPowerCoeffs,
      blogPowerScale, decimalNat]
    ring
  have hpositive := positive_of_certificate
    5 56 blogIdentityScale blogPowerScale 3 2
    blogPowerCoeffs blogBernsteinCoeffs
    (by norm_num) (by
      norm_num [blogIdentityScale, decimalNat]) (by
      norm_num [blogPowerScale, decimalNat])
    (by norm_num [blogPowerCoeffs])
    (by norm_num [blogBernsteinCoeffs, decimalNat])
    (by norm_num [blogBernsteinCoeffs, decimalNat])
    blog_polynomial_identity u z
    (backwardBLogLowerScaledThree (2 / 25) (r1Back2TReal z) -
      backwardBLogFitRound1Back2 z)
    (backwardBLogDenRound1Back2 z) hu hpoint hden hrat
  exact sub_pos.mp hpositive

private lemma xlog_le_tangent {pCenter omCenter z : ℝ}
    (hz : z ∈ Set.Icc (3 / 5 : ℝ) 1)
    (hpCenter : pCenter ∈ Set.Ioc (0 : ℝ) 1)
    (homCenter : omCenter ∈ Set.Ioc (0 : ℝ) 1) :
    tangentXLog (9 / 200) z ≤
      backwardXLogTangentUpper pCenter omCenter
        (backwardBlueFitRound1Back2 z) z := by
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hfit := blue_fit_le_raw hz
  have hraw := backward_blue_raw_lower_le
    (β := (9 / 200 : ℝ)) (z := z) (by norm_num) hzunit
  obtain ⟨hB0, hB1⟩ := round1_back2_blue_fit_bounds hz
  exact tangent_xlog_le_backward_tangent_nine
    (β := (9 / 200 : ℝ)) (z := z)
    (B := backwardBlueFitRound1Back2 z)
    (pCenter := pCenter) (omCenter := omCenter)
    (by norm_num) hzunit hpCenter homCenter hB0.le
    (hfit.trans hraw) hB1

private lemma backward_mu_lower_nine_lt_one {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    backwardMuLowerNine z < 1 := by
  have happrox := KernelBounds.exp_neg_approx hz
  have hM :
      backwardMuLowerNine z ≤ optimizationM z := by
    unfold backwardMuLowerNine optimizationM
    exact mul_le_mul_of_nonneg_left
      (by linarith [abs_le.mp happrox]) hz.1
  exact hM.trans_lt
    (optimizationM_lt_one_of_Icc hz.1 hz.2)

private lemma x_piece_certificate_pos
    (left : ℤ) (identityScale powerScale : ℕ)
    (powerCoefficients : List ℤ)
    (bernsteinCoefficients : List ℕ)
    (hidentityScale : identityScale ≠ 0)
    (hpowerScale : powerScale ≠ 0)
    (hlength : powerCoefficients.length = 23)
    (hfirst : 0 < bernsteinCoefficients.getD 0 0)
    (hlast : 0 < bernsteinCoefficients.getD 22 0)
    (hidentity :
      ((identityScale : ℤ) : Polynomial ℤ) *
          homogenizedAffine 20 left 1 powerCoefficients =
        (20 ^ 22 : Polynomial ℤ) *
          BackwardCoordRound1Back2Certificate.bernsteinPolynomial
            22 bernsteinCoefficients)
    (u z pCenter omCenter : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hpoint : ((left : ℝ) + u) / 20 = z)
    (hzunit : z ∈ Set.Icc (0 : ℝ) 1)
    (hrat :
      backwardBLogFitRound1Back2 z -
          backwardXLogTangentUpper pCenter omCenter
            (backwardBlueFitRound1Back2 z) z =
        (evalPower powerCoefficients z / powerScale) /
          (1 - backwardMuLowerNine z)) :
    backwardXLogTangentUpper pCenter omCenter
        (backwardBlueFitRound1Back2 z) z <
      backwardBLogFitRound1Back2 z := by
  have hM1 := backward_mu_lower_nine_lt_one hzunit
  have hden : 0 < 1 - backwardMuLowerNine z :=
    sub_pos.mpr hM1
  have hpositive := positive_of_certificate
    20 22 identityScale powerScale left 1
    powerCoefficients bernsteinCoefficients
    (by norm_num) hidentityScale hpowerScale hlength
    hfirst hlast hidentity u z
    (backwardBLogFitRound1Back2 z -
      backwardXLogTangentUpper pCenter omCenter
        (backwardBlueFitRound1Back2 z) z)
    (1 - backwardMuLowerNine z) hu (by simpa using hpoint)
    hden hrat
  exact sub_pos.mp hpositive

set_option maxHeartbeats 0 in
-- Expanding the degree-22 first X-log piece exceeds the default heartbeat budget.
set_option maxRecDepth 30000 in
-- The exact rational identity also needs additional simplifier recursion.
private lemma x_piece_zero_pos {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 5 : ℝ) (13 / 20)) :
    backwardXLogTangentUpper
        (619453 / 1000000) (166423 / 250000)
        (backwardBlueFitRound1Back2 z) z <
      backwardBLogFitRound1Back2 z := by
  let u : ℝ := 20 * z - 12
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hpoint : ((12 + u) / 20 : ℝ) = z := by
    dsimp [u]
    ring
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hM1 := backward_mu_lower_nine_lt_one hzunit
  have hden : 0 < 1 - backwardMuLowerNine z :=
    sub_pos.mpr hM1
  have hrat :
      backwardBLogFitRound1Back2 z -
          backwardXLogTangentUpper
            (619453 / 1000000) (166423 / 250000)
            (backwardBlueFitRound1Back2 z) z =
        (evalPower x0PowerCoeffs z / x0PowerScale) /
          (1 - backwardMuLowerNine z) := by
    apply (eq_div_iff hden.ne').2
    unfold backwardXLogTangentUpper
      backwardLogTangentUpper backwardLogUpperBelowSeven
    dsimp only
    field_simp [hden.ne']
    unfold backwardMuLowerNine backwardBlueFitRound1Back2
      backwardBLogFitRound1Back2
    norm_num [KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Finset.sum_range_succ,
      Nat.factorial]
    dsimp [evalPower, x0PowerCoeffs, x0PowerScale, decimalNat]
    ring
  have hpositive := positive_of_certificate
    20 22 x0IdentityScale x0PowerScale 12 1
    x0PowerCoeffs x0BernsteinCoeffs
    (by norm_num) (by
      norm_num [x0IdentityScale, decimalNat]) (by
      norm_num [x0PowerScale, decimalNat])
    (by norm_num [x0PowerCoeffs])
    (by norm_num [x0BernsteinCoeffs, decimalNat])
    (by norm_num [x0BernsteinCoeffs, decimalNat])
    x0_polynomial_identity u z
    (backwardBLogFitRound1Back2 z -
      backwardXLogTangentUpper
        (619453 / 1000000) (166423 / 250000)
        (backwardBlueFitRound1Back2 z) z)
    (1 - backwardMuLowerNine z) hu (by simpa using hpoint) hden hrat
  exact sub_pos.mp hpositive

set_option maxHeartbeats 0 in
-- Expanding the degree-22 second X-log piece exceeds the default heartbeat budget.
set_option maxRecDepth 30000 in
-- The exact rational identity also needs additional simplifier recursion.
private lemma x_piece_one_pos {z : ℝ}
    (hz : z ∈ Set.Icc (13 / 20 : ℝ) (7 / 10)) :
    backwardXLogTangentUpper
        (303009 / 500000) (65653 / 100000)
        (backwardBlueFitRound1Back2 z) z <
      backwardBLogFitRound1Back2 z := by
  let u : ℝ := 20 * z - 13
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hpoint : ((13 + u) / 20 : ℝ) = z := by
    dsimp [u]
    ring
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hden : 0 < 1 - backwardMuLowerNine z :=
    sub_pos.mpr (backward_mu_lower_nine_lt_one hzunit)
  have hrat :
      backwardBLogFitRound1Back2 z -
          backwardXLogTangentUpper
            (303009 / 500000) (65653 / 100000)
            (backwardBlueFitRound1Back2 z) z =
        (evalPower x1PowerCoeffs z / x1PowerScale) /
          (1 - backwardMuLowerNine z) := by
    apply (eq_div_iff hden.ne').2
    unfold backwardXLogTangentUpper
      backwardLogTangentUpper backwardLogUpperBelowSeven
    dsimp only
    field_simp [hden.ne']
    unfold backwardMuLowerNine backwardBlueFitRound1Back2
      backwardBLogFitRound1Back2
    norm_num [KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Finset.sum_range_succ,
      Nat.factorial]
    dsimp [evalPower, x1PowerCoeffs, x1PowerScale, decimalNat]
    ring
  exact x_piece_certificate_pos 13
    x1IdentityScale x1PowerScale
    x1PowerCoeffs x1BernsteinCoeffs
    (by norm_num [x1IdentityScale, decimalNat])
    (by norm_num [x1PowerScale, decimalNat])
    (by norm_num [x1PowerCoeffs])
    (by norm_num [x1BernsteinCoeffs, decimalNat])
    (by norm_num [x1BernsteinCoeffs, decimalNat])
    x1_polynomial_identity u z
    (303009 / 500000) (65653 / 100000)
    hu (by simpa using hpoint) hzunit hrat

set_option maxHeartbeats 0 in
-- Expanding the degree-22 third X-log piece exceeds the default heartbeat budget.
set_option maxRecDepth 30000 in
-- The exact rational identity also needs additional simplifier recursion.
private lemma x_piece_two_pos {z : ℝ}
    (hz : z ∈ Set.Icc (7 / 10 : ℝ) (3 / 4)) :
    backwardXLogTangentUpper
        (296767 / 500000) (324529 / 500000)
        (backwardBlueFitRound1Back2 z) z <
      backwardBLogFitRound1Back2 z := by
  let u : ℝ := 20 * z - 14
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hpoint : ((14 + u) / 20 : ℝ) = z := by
    dsimp [u]
    ring
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hden : 0 < 1 - backwardMuLowerNine z :=
    sub_pos.mpr (backward_mu_lower_nine_lt_one hzunit)
  have hrat :
      backwardBLogFitRound1Back2 z -
          backwardXLogTangentUpper
            (296767 / 500000) (324529 / 500000)
            (backwardBlueFitRound1Back2 z) z =
        (evalPower x2PowerCoeffs z / x2PowerScale) /
          (1 - backwardMuLowerNine z) := by
    apply (eq_div_iff hden.ne').2
    unfold backwardXLogTangentUpper
      backwardLogTangentUpper backwardLogUpperBelowSeven
    dsimp only
    field_simp [hden.ne']
    unfold backwardMuLowerNine backwardBlueFitRound1Back2
      backwardBLogFitRound1Back2
    norm_num [KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Finset.sum_range_succ,
      Nat.factorial]
    dsimp [evalPower, x2PowerCoeffs, x2PowerScale, decimalNat]
    ring
  exact x_piece_certificate_pos 14
    x2IdentityScale x2PowerScale
    x2PowerCoeffs x2BernsteinCoeffs
    (by norm_num [x2IdentityScale, decimalNat])
    (by norm_num [x2PowerScale, decimalNat])
    (by norm_num [x2PowerCoeffs])
    (by norm_num [x2BernsteinCoeffs, decimalNat])
    (by norm_num [x2BernsteinCoeffs, decimalNat])
    x2_polynomial_identity u z
    (296767 / 500000) (324529 / 500000)
    hu (by simpa using hpoint) hzunit hrat

set_option maxHeartbeats 0 in
-- Expanding the degree-22 fourth X-log piece exceeds the default heartbeat budget.
set_option maxRecDepth 30000 in
-- The exact rational identity also needs additional simplifier recursion.
private lemma x_piece_three_pos {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 4 : ℝ) (4 / 5)) :
    backwardXLogTangentUpper
        (581857 / 1000000) (643131 / 1000000)
        (backwardBlueFitRound1Back2 z) z <
      backwardBLogFitRound1Back2 z := by
  let u : ℝ := 20 * z - 15
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hpoint : ((15 + u) / 20 : ℝ) = z := by
    dsimp [u]
    ring
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hden : 0 < 1 - backwardMuLowerNine z :=
    sub_pos.mpr (backward_mu_lower_nine_lt_one hzunit)
  have hrat :
      backwardBLogFitRound1Back2 z -
          backwardXLogTangentUpper
            (581857 / 1000000) (643131 / 1000000)
            (backwardBlueFitRound1Back2 z) z =
        (evalPower x3PowerCoeffs z / x3PowerScale) /
          (1 - backwardMuLowerNine z) := by
    apply (eq_div_iff hden.ne').2
    unfold backwardXLogTangentUpper
      backwardLogTangentUpper backwardLogUpperBelowSeven
    dsimp only
    field_simp [hden.ne']
    unfold backwardMuLowerNine backwardBlueFitRound1Back2
      backwardBLogFitRound1Back2
    norm_num [KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Finset.sum_range_succ,
      Nat.factorial]
    dsimp [evalPower, x3PowerCoeffs, x3PowerScale, decimalNat]
    ring
  exact x_piece_certificate_pos 15
    x3IdentityScale x3PowerScale
    x3PowerCoeffs x3BernsteinCoeffs
    (by norm_num [x3IdentityScale, decimalNat])
    (by norm_num [x3PowerScale, decimalNat])
    (by norm_num [x3PowerCoeffs])
    (by norm_num [x3BernsteinCoeffs, decimalNat])
    (by norm_num [x3BernsteinCoeffs, decimalNat])
    x3_polynomial_identity u z
    (581857 / 1000000) (643131 / 1000000)
    hu (by simpa using hpoint) hzunit hrat

set_option maxHeartbeats 0 in
-- Expanding the degree-22 fifth X-log piece exceeds the default heartbeat budget.
set_option maxRecDepth 30000 in
-- The exact rational identity also needs additional simplifier recursion.
private lemma x_piece_four_pos {z : ℝ}
    (hz : z ∈ Set.Icc (4 / 5 : ℝ) (17 / 20)) :
    backwardXLogTangentUpper
        (570863 / 1000000) (638617 / 1000000)
        (backwardBlueFitRound1Back2 z) z <
      backwardBLogFitRound1Back2 z := by
  let u : ℝ := 20 * z - 16
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hpoint : ((16 + u) / 20 : ℝ) = z := by
    dsimp [u]
    ring
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hden : 0 < 1 - backwardMuLowerNine z :=
    sub_pos.mpr (backward_mu_lower_nine_lt_one hzunit)
  have hrat :
      backwardBLogFitRound1Back2 z -
          backwardXLogTangentUpper
            (570863 / 1000000) (638617 / 1000000)
            (backwardBlueFitRound1Back2 z) z =
        (evalPower x4PowerCoeffs z / x4PowerScale) /
          (1 - backwardMuLowerNine z) := by
    apply (eq_div_iff hden.ne').2
    unfold backwardXLogTangentUpper
      backwardLogTangentUpper backwardLogUpperBelowSeven
    dsimp only
    field_simp [hden.ne']
    unfold backwardMuLowerNine backwardBlueFitRound1Back2
      backwardBLogFitRound1Back2
    norm_num [KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Finset.sum_range_succ,
      Nat.factorial]
    dsimp [evalPower, x4PowerCoeffs, x4PowerScale, decimalNat]
    ring
  exact x_piece_certificate_pos 16
    x4IdentityScale x4PowerScale
    x4PowerCoeffs x4BernsteinCoeffs
    (by norm_num [x4IdentityScale, decimalNat])
    (by norm_num [x4PowerScale, decimalNat])
    (by norm_num [x4PowerCoeffs])
    (by norm_num [x4BernsteinCoeffs, decimalNat])
    (by norm_num [x4BernsteinCoeffs, decimalNat])
    x4_polynomial_identity u z
    (570863 / 1000000) (638617 / 1000000)
    hu (by simpa using hpoint) hzunit hrat

set_option maxHeartbeats 0 in
-- Expanding the degree-22 sixth X-log piece exceeds the default heartbeat budget.
set_option maxRecDepth 30000 in
-- The exact rational identity also needs additional simplifier recursion.
private lemma x_piece_five_pos {z : ℝ}
    (hz : z ∈ Set.Icc (17 / 20 : ℝ) (9 / 10)) :
    backwardXLogTangentUpper
        (560443 / 1000000) (9928 / 15625)
        (backwardBlueFitRound1Back2 z) z <
      backwardBLogFitRound1Back2 z := by
  let u : ℝ := 20 * z - 17
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hpoint : ((17 + u) / 20 : ℝ) = z := by
    dsimp [u]
    ring
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hden : 0 < 1 - backwardMuLowerNine z :=
    sub_pos.mpr (backward_mu_lower_nine_lt_one hzunit)
  have hrat :
      backwardBLogFitRound1Back2 z -
          backwardXLogTangentUpper
            (560443 / 1000000) (9928 / 15625)
            (backwardBlueFitRound1Back2 z) z =
        (evalPower x5PowerCoeffs z / x5PowerScale) /
          (1 - backwardMuLowerNine z) := by
    apply (eq_div_iff hden.ne').2
    unfold backwardXLogTangentUpper
      backwardLogTangentUpper backwardLogUpperBelowSeven
    dsimp only
    field_simp [hden.ne']
    unfold backwardMuLowerNine backwardBlueFitRound1Back2
      backwardBLogFitRound1Back2
    norm_num [KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Finset.sum_range_succ,
      Nat.factorial]
    dsimp [evalPower, x5PowerCoeffs, x5PowerScale, decimalNat]
    ring
  exact x_piece_certificate_pos 17
    x5IdentityScale x5PowerScale
    x5PowerCoeffs x5BernsteinCoeffs
    (by norm_num [x5IdentityScale, decimalNat])
    (by norm_num [x5PowerScale, decimalNat])
    (by norm_num [x5PowerCoeffs])
    (by norm_num [x5BernsteinCoeffs, decimalNat])
    (by norm_num [x5BernsteinCoeffs, decimalNat])
    x5_polynomial_identity u z
    (560443 / 1000000) (9928 / 15625)
    hu (by simpa using hpoint) hzunit hrat

set_option maxHeartbeats 0 in
-- Expanding the degree-22 seventh X-log piece exceeds the default heartbeat budget.
set_option maxRecDepth 30000 in
-- The exact rational identity also needs additional simplifier recursion.
private lemma x_piece_six_pos {z : ℝ}
    (hz : z ∈ Set.Icc (9 / 10 : ℝ) (19 / 20)) :
    backwardXLogTangentUpper
        (55051 / 100000) (316671 / 500000)
        (backwardBlueFitRound1Back2 z) z <
      backwardBLogFitRound1Back2 z := by
  let u : ℝ := 20 * z - 18
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hpoint : ((18 + u) / 20 : ℝ) = z := by
    dsimp [u]
    ring
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hden : 0 < 1 - backwardMuLowerNine z :=
    sub_pos.mpr (backward_mu_lower_nine_lt_one hzunit)
  have hrat :
      backwardBLogFitRound1Back2 z -
          backwardXLogTangentUpper
            (55051 / 100000) (316671 / 500000)
            (backwardBlueFitRound1Back2 z) z =
        (evalPower x6PowerCoeffs z / x6PowerScale) /
          (1 - backwardMuLowerNine z) := by
    apply (eq_div_iff hden.ne').2
    unfold backwardXLogTangentUpper
      backwardLogTangentUpper backwardLogUpperBelowSeven
    dsimp only
    field_simp [hden.ne']
    unfold backwardMuLowerNine backwardBlueFitRound1Back2
      backwardBLogFitRound1Back2
    norm_num [KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Finset.sum_range_succ,
      Nat.factorial]
    dsimp [evalPower, x6PowerCoeffs, x6PowerScale, decimalNat]
    ring
  exact x_piece_certificate_pos 18
    x6IdentityScale x6PowerScale
    x6PowerCoeffs x6BernsteinCoeffs
    (by norm_num [x6IdentityScale, decimalNat])
    (by norm_num [x6PowerScale, decimalNat])
    (by norm_num [x6PowerCoeffs])
    (by norm_num [x6BernsteinCoeffs, decimalNat])
    (by norm_num [x6BernsteinCoeffs, decimalNat])
    x6_polynomial_identity u z
    (55051 / 100000) (316671 / 500000)
    hu (by simpa using hpoint) hzunit hrat

set_option maxHeartbeats 0 in
-- Expanding the degree-22 eighth X-log piece exceeds the default heartbeat budget.
set_option maxRecDepth 30000 in
-- The exact rational identity also needs additional simplifier recursion.
private lemma x_piece_seven_pos {z : ℝ}
    (hz : z ∈ Set.Icc (19 / 20 : ℝ) 1) :
    backwardXLogTangentUpper
        (8453 / 15625) (632359 / 1000000)
        (backwardBlueFitRound1Back2 z) z <
      backwardBLogFitRound1Back2 z := by
  let u : ℝ := 20 * z - 19
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hpoint : ((19 + u) / 20 : ℝ) = z := by
    dsimp [u]
    ring
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hden : 0 < 1 - backwardMuLowerNine z :=
    sub_pos.mpr (backward_mu_lower_nine_lt_one hzunit)
  have hrat :
      backwardBLogFitRound1Back2 z -
          backwardXLogTangentUpper
            (8453 / 15625) (632359 / 1000000)
            (backwardBlueFitRound1Back2 z) z =
        (evalPower x7PowerCoeffs z / x7PowerScale) /
          (1 - backwardMuLowerNine z) := by
    apply (eq_div_iff hden.ne').2
    unfold backwardXLogTangentUpper
      backwardLogTangentUpper backwardLogUpperBelowSeven
    dsimp only
    field_simp [hden.ne']
    unfold backwardMuLowerNine backwardBlueFitRound1Back2
      backwardBLogFitRound1Back2
    norm_num [KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Finset.sum_range_succ,
      Nat.factorial]
    dsimp [evalPower, x7PowerCoeffs, x7PowerScale, decimalNat]
    ring
  exact x_piece_certificate_pos 19
    x7IdentityScale x7PowerScale
    x7PowerCoeffs x7BernsteinCoeffs
    (by norm_num [x7IdentityScale, decimalNat])
    (by norm_num [x7PowerScale, decimalNat])
    (by norm_num [x7PowerCoeffs])
    (by norm_num [x7BernsteinCoeffs, decimalNat])
    (by norm_num [x7BernsteinCoeffs, decimalNat])
    x7_polynomial_identity u z
    (8453 / 15625) (632359 / 1000000)
    hu (by simpa using hpoint) hzunit hrat

/-- The first-round coordinate inequality on the second backward interval. -/
lemma tangent_backward_coord_round1_back2 :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      tangentXLog (9 / 200) z ≤
        tangentBLog (2 / 25) (r1Back2TReal z) := by
  intro z hz
  obtain ⟨ht0, htHalf⟩ := round1_back2_t_bounds hz
  have hblogFit := blog_fit_lt_lower hz
  have hblog := backward_blog_lower_scaled_three_le
    (β := (2 / 25 : ℝ)) (t := r1Back2TReal z)
    (by norm_num) ⟨ht0.le, htHalf⟩ ht0
  by_cases hzero : z ≤ 13 / 20
  · have hpiece := x_piece_zero_pos ⟨hz.1, hzero⟩
    have hx := xlog_le_tangent hz
      (show (619453 / 1000000 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
      (show (166423 / 250000 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
    linarith
  by_cases hone : z ≤ 7 / 10
  · have hpiece := x_piece_one_pos
      ⟨(by linarith : (13 / 20 : ℝ) ≤ z), hone⟩
    have hx := xlog_le_tangent hz
      (show (303009 / 500000 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
      (show (65653 / 100000 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
    linarith
  by_cases htwo : z ≤ 3 / 4
  · have hpiece := x_piece_two_pos
      ⟨(by linarith : (7 / 10 : ℝ) ≤ z), htwo⟩
    have hx := xlog_le_tangent hz
      (show (296767 / 500000 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
      (show (324529 / 500000 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
    linarith
  by_cases hthree : z ≤ 4 / 5
  · have hpiece := x_piece_three_pos
      ⟨(by linarith : (3 / 4 : ℝ) ≤ z), hthree⟩
    have hx := xlog_le_tangent hz
      (show (581857 / 1000000 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
      (show (643131 / 1000000 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
    linarith
  by_cases hfour : z ≤ 17 / 20
  · have hpiece := x_piece_four_pos
      ⟨(by linarith : (4 / 5 : ℝ) ≤ z), hfour⟩
    have hx := xlog_le_tangent hz
      (show (570863 / 1000000 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
      (show (638617 / 1000000 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
    linarith
  by_cases hfive : z ≤ 9 / 10
  · have hpiece := x_piece_five_pos
      ⟨(by linarith : (17 / 20 : ℝ) ≤ z), hfive⟩
    have hx := xlog_le_tangent hz
      (show (560443 / 1000000 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
      (show (9928 / 15625 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
    linarith
  by_cases hsix : z ≤ 19 / 20
  · have hpiece := x_piece_six_pos
      ⟨(by linarith : (9 / 10 : ℝ) ≤ z), hsix⟩
    have hx := xlog_le_tangent hz
      (show (55051 / 100000 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
      (show (316671 / 500000 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
    linarith
  · have hpiece := x_piece_seven_pos
      ⟨(by linarith : (19 / 20 : ℝ) ≤ z), hz.2⟩
    have hx := xlog_le_tangent hz
      (show (8453 / 15625 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
      (show (632359 / 1000000 : ℝ) ∈ Set.Ioc 0 1 by
        norm_num)
    linarith

end

end BackwardCoordRound1Back2Bounds
end Arxiv2407_19026
