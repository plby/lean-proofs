import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back1Certificate
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound1Back1Bounds

/-!
# First-round first backward book bound

This file connects the exact blue-fit and book-margin certificates to the
semantic inequality on `[0.387, 0.6]`.
-/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back1Bounds

noncomputable section

open BackwardBookRound1Back1Certificate

def backwardBlueUpperRound1Back1 (z : ℝ) : ℝ :=
  10865412772 / 1000000000000 +
    290214906559 / 250000000000 * z -
    29154435911 / 20000000000 * z ^ 2 +
    136898472756 / 125000000000 * z ^ 3 -
    87922281309 / 250000000000 * z ^ 4

private lemma evalPower_eq_bernstein_of_identity
    (degree denominator : ℕ) (left width : ℤ)
    (scale : ℕ) (coefficients : List ℤ)
    (bernsteinCoefficients : List ℕ)
    (hdenominator : denominator ≠ 0)
    (hscale : scale ≠ 0)
    (hlength : coefficients.length = degree + 1)
    (hidentity :
      integerPowerScale scale
          (integerPowerAffine denominator left width coefficients) =
        integerPowerScale (denominator ^ degree : ℤ)
          (integerPowerBernstein degree bernsteinCoefficients))
    (u : ℝ) :
    evalPower coefficients
        (((left : ℝ) + (width : ℝ) * u) / denominator) =
      (∑ i ∈ Finset.range (degree + 1),
        (bernsteinCoefficients.getD i 0 : ℝ) *
          u ^ i * (1 - u) ^ (degree - i)) / scale := by
  have h := evalIntegerPower_affine_bernstein
    denominator degree scale left width coefficients
    bernsteinCoefficients u hdenominator hlength hidentity
  rw [eq_div_iff (by exact_mod_cast hscale)]
  simpa [evalPower, mul_comm] using h

private lemma blue_fit_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5)) :
    0 < backwardBlueUpperRound1Back1 z ∧
      backwardBlueUpperRound1Back1 z < 1 := by
  let u : ℝ := (1000 * z - 387) / 213
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hfit :
      backwardBlueUpperRound1Back1 z =
        (74346411186356037006451 /
            250000000000000000000000 : ℝ) *
            (1 - u) ^ 4 +
          401227366599471440939 /
              312500000000000000000 *
            u * (1 - u) ^ 3 +
          25558533173770729077 /
              12500000000000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          22381993998389863 / 15625000000000000 *
            u ^ 3 * (1 - u) +
          116744685127307 / 312500000000000 *
            u ^ 4 := by
    dsimp [u, backwardBlueUpperRound1Back1]
    ring
  have hone :
      1 - backwardBlueUpperRound1Back1 z =
        (175653588813643962993549 /
            250000000000000000000000 : ℝ) *
            (1 - u) ^ 4 +
          848772633400528559061 /
              312500000000000000000 *
            u * (1 - u) ^ 3 +
          49441466826229270923 /
              12500000000000000000 *
            u ^ 2 * (1 - u) ^ 2 +
          40118006001610137 / 15625000000000000 *
            u ^ 3 * (1 - u) +
          195755314872693 / 312500000000000 *
            u ^ 4 := by
    dsimp [u, backwardBlueUpperRound1Back1]
    ring
  constructor
  · rw [hfit]
    by_cases hzero : u = 0
    · simp [hzero]
    · have hupos : 0 < u :=
        lt_of_le_of_ne hu0 (Ne.symm hzero)
      positivity
  · rw [← sub_pos, hone]
    by_cases hzero : u = 0
    · simp [hzero]
    · have hupos : 0 < u :=
        lt_of_le_of_ne hu0 (Ne.symm hzero)
      positivity

set_option maxHeartbeats 0 in
-- Expanding the exact degree-49 blue-fit certificate exceeds the default heartbeat budget.
set_option maxRecDepth 30000 in
-- The exact rational identity also needs additional simplifier recursion.
private lemma raw_blue_le_fit {z : ℝ}
    (hz : z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5)) :
    backwardBlueRawUpper (9 / 200) z ≤
      backwardBlueUpperRound1Back1 z := by
  let u : ℝ := (1000 * z - 387) / 213
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 49
    blueBernsteinCoeffs hu (by
      norm_num [blueBernsteinCoeffs, decimalNat]) (by
      norm_num [blueBernsteinCoeffs, decimalNat])
  have hpower := evalPower_eq_bernstein_of_identity
    49 1000 387 213 blueIdentityScale
    bluePowerCoeffs blueBernsteinCoeffs
    (by norm_num) (by
      norm_num [blueIdentityScale, decimalNat])
    (by norm_num [bluePowerCoeffs])
    blue_integer_identity u
  have hzFromU :
      ((387 + 213 * u) / 1000 : ℝ) = z := by
    dsimp [u]
    ring
  norm_num at hpower
  rw [hzFromU] at hpower
  have hzplus : 0 < 1 + z := by
    nlinarith [hz.1]
  have hrat :
      backwardBlueUpperRound1Back1 z -
          backwardBlueRawUpper (9 / 200) z =
        (evalPower bluePowerCoeffs z / bluePowerScale) /
          (1 + z) := by
    dsimp [backwardBlueRawUpper, backwardExpQUpper,
      backwardQUpper, mediumCorrectionPolynomial,
      backwardBlueUpperRound1Back1]
    norm_num [KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Finset.sum_range_succ,
      Nat.factorial]
    dsimp [evalPower, bluePowerCoeffs, bluePowerScale,
      decimalNat]
    field_simp [hzplus.ne']
    simp only [evalIntegerPower]
    ring_nf
  rw [← sub_nonneg, hrat, hpower]
  have hIdentityScale : (0 : ℝ) < blueIdentityScale := by
    norm_num [blueIdentityScale, decimalNat]
  have hPowerScale : (0 : ℝ) < bluePowerScale := by
    norm_num [bluePowerScale, decimalNat]
  positivity

private lemma backward_book_lower_pos {z : ℝ}
    (hz : z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5)) :
    0 < backwardBookLowerTwo (2 / 25) (9 / 200)
      (r1Back1TReal z) (backwardBlueUpperRound1Back1 z) z := by
  let u : ℝ := (1000 * z - 387) / 213
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have huInterval :
      u ∈
        ({ lo := 0, hi := 1, le := by norm_num } :
          LeanCert.Core.IntervalRat) := by
    simpa [LeanCert.Core.IntervalRat.mem_def] using hu
  have hpower : 0 < evalIntegerPower bookPowerCoeffs u :=
    eval_integer_power_pos_of_interval bookPowerCoeffs
      ({ lo := 0, hi := 1, le := by norm_num } :
        LeanCert.Core.IntervalRat)
      huInterval book_horner_lower
  obtain ⟨hB0, hB1⟩ := blue_fit_bounds hz
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  obtain ⟨_, hM0, hM1⟩ :=
    backward_mu_upper_nine_bounds hzunit
  have hzplus2 : 0 < z + 2 := by
    nlinarith [hz.1]
  have hBsub1 : 0 < 1 - backwardBlueUpperRound1Back1 z :=
    sub_pos.mpr hB1
  have hBsub2 : 0 < 2 - backwardBlueUpperRound1Back1 z := by
    linarith
  have hMsub1 : 0 < 1 - backwardMuUpperNine z :=
    sub_pos.mpr hM1
  have hMsub2 : 0 < 2 - backwardMuUpperNine z := by
    linarith
  have hAffinePoint :
      ((387 : ℝ) + 213 * u) / 1000 = z := by
    dsimp [u]
    ring
  have hNumeratorInteger :
      0 < evalIntegerPower bookNumeratorCoeffs z := by
    have hAffine := book_affine_eval u
    rw [hAffinePoint] at hAffine
    have hProduct :
        0 <
          evalIntegerPower bookPowerCoeffs u * 1000 :=
      mul_pos hpower (by norm_num)
    rw [hAffine] at hProduct
    rcases mul_pos_iff.mp hProduct with hpositive | hnegative
    · exact hpositive.2
    · exact (not_lt_of_ge (by positivity) hnegative.1).elim
  have hNumeratorExpanded :
      0 < rationalPowerEval bookNumeratorExpandedPower z := by
    rw [book_numerator_integer_eval]
    apply div_pos hNumeratorInteger
    norm_num [bookNumeratorScale, decimalNat]
  have hNumerator :
      0 <
        rationalPowerEval
          (backwardBookNumeratorTwoPower
            (2 / 25) (9 / 200) bookTPower bookBluePower) z := by
    rw [book_numerator_eval]
    exact hNumeratorExpanded
  have htEval :
      rationalPowerEval bookTPower z = r1Back1TReal z := by
    rw [bookTPower, rationalPowerEval_comp]
    norm_num [rationalPowerEval, r1Back1TReal,
      tangentLocalPoly, tangentRatHorner,
      TangentAffine.r1Back1Cs]
    ring
  have hblueEval :
      rationalPowerEval bookBluePower z =
        backwardBlueUpperRound1Back1 z := by
    norm_num [bookBluePower, rationalPowerEval,
      backwardBlueUpperRound1Back1]
    ring
  have hDenominator :
      0 <
        rationalPowerEval
          (backwardBookDenominatorTwoPower bookBluePower) z := by
    rw [backwardBookDenominatorTwoPower,
      rationalPowerEval_mul]
    apply mul_pos
    · rw [backwardEntropyDenominatorPower_eval]
      exact pow_pos hzplus2 9
    · rw [rationalPowerEval_mul]
      apply mul_pos
      · rw [backwardLogTwoDenominatorPower_eval,
          hblueEval]
        exact mul_pos
          (mul_pos (by norm_num) (pow_pos hBsub2 3))
          hBsub1
      · rw [backwardLogTwoDenominatorPower_eval,
          backwardMuPower_eval]
        exact mul_pos
          (mul_pos (by norm_num) (pow_pos hMsub2 3))
          hMsub1
  have hBPowerSub1 :
      0 < 1 - rationalPowerEval bookBluePower z := by
    rw [hblueEval]
    exact hBsub1
  have hBPowerSub2 :
      0 < 2 - rationalPowerEval bookBluePower z := by
    rw [hblueEval]
    exact hBsub2
  have hBridge :=
    backwardBookNumeratorTwoPower_eval_closed
      (2 / 25) (9 / 200) bookTPower bookBluePower z
      hzplus2.ne' hBPowerSub1.ne' hBPowerSub2.ne'
      hMsub1.ne' hMsub2.ne'
  rw [htEval, hblueEval] at hBridge
  have hClosedCast :
      0 <
        backwardBookLowerTwoClosed
          ((2 / 25 : ℚ) : ℝ) ((9 / 200 : ℚ) : ℝ)
          (r1Back1TReal z)
          (backwardBlueUpperRound1Back1 z) z := by
    rw [← hBridge]
    exact div_pos hNumerator hDenominator
  norm_num at hClosedCast
  have hClosed :
      0 <
        backwardBookLowerTwoClosed
          (2 / 25) (9 / 200) (r1Back1TReal z)
          (backwardBlueUpperRound1Back1 z) z :=
    hClosedCast
  rw [backwardBookLowerTwo_eq_closed
    (2 / 25) (9 / 200) (r1Back1TReal z)
    (backwardBlueUpperRound1Back1 z) z
    hB0.le hB1 hM0 hM1]
  exact hClosed

/-- The book inequality on the first-round first backward interval. -/
lemma tangent_backward_book_round1_back1 :
    ∀ z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5),
      0 < tangentCleanBookMargin (9 / 200) z
        (tangentALog (2 / 25) (r1Back1TReal z) -
          Real.log z) := by
  intro z hz
  obtain ⟨ht0, ht1⟩ :=
    BackwardCoordRound1Back1Bounds.round1_back1_t_bounds hz
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  obtain ⟨hB0, hB1⟩ := blue_fit_bounds hz
  have hblueRaw := raw_blue_le_fit hz
  have hblue := (tangent_blue_le_backward_raw_upper
    (β := (9 / 200 : ℝ)) (z := z) (by norm_num)
    hzunit).trans hblueRaw
  exact (backward_book_lower_pos hz).trans_le
    (backward_book_lower_two_le
      (by norm_num) (by norm_num) hzunit
      (by nlinarith [hz.1])
      ⟨ht0.le, ht1.le⟩ hB0.le hblue hB1)

end

end BackwardBookRound1Back1Bounds
end Arxiv2407_19026
