import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back1RightCertificate
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound3Back1Bounds

/-!
# Round 3, backward book interval 1

This file connects the exact blue-fit and book-margin certificates to the
semantic inequality on `[0.375, 0.6]`.
-/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back1Bounds

noncomputable section

open BackwardBookRound3Back1Certificate

def backwardBlueUpperRound3Back1 (z : ℝ) : ℝ :=
  (488949191 / 50000000000) +
    (29299073871 / 25000000000) * z +
    (-91730535159 / 62500000000) * z ^ 2 +
    (1098786664063 / 1000000000000) * z ^ 3 +
    (-176510583707 / 500000000000) * z ^ 4

private lemma evalPower_eq_bernstein_of_identity
    (degree denominator : ℕ) (left width : ℤ)
    (scale : ℕ) (coefficients : List ℤ)
    (bernsteinCoefficients : List ℕ)
    (hdenominator : denominator ≠ 0)
    (hscale : scale ≠ 0)
    (hlength : coefficients.length = degree + 1)
    (hidentity :
      ((scale : ℤ) : Polynomial ℤ) *
          homogenizedAffine denominator left width coefficients =
        (denominator ^ degree : Polynomial ℤ) *
          BackwardBookRound3Back1Certificate.bernsteinPolynomial
            degree bernsteinCoefficients)
    (u : ℝ) :
    evalPower coefficients
        (((left : ℝ) + (width : ℝ) * u) / denominator) =
      (∑ i ∈ Finset.range (degree + 1),
        (bernsteinCoefficients.getD i 0 : ℝ) *
          u ^ i * (1 - u) ^ (degree - i)) / scale := by
  have hBernstein :
      Polynomial.eval₂ (Int.castRingHom ℝ) u
          (BackwardBookRound3Back1Certificate.bernsteinPolynomial
            degree bernsteinCoefficients) =
        ∑ i ∈ Finset.range (degree + 1),
          (bernsteinCoefficients.getD i 0 : ℝ) *
            u ^ i * (1 - u) ^ (degree - i) := by
    dsimp [BackwardBookRound3Back1Certificate.bernsteinPolynomial]
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
            (((left : ℝ) + (width : ℝ) * u) /
              denominator) := by
    have hdenominatorReal : (denominator : ℝ) ≠ 0 := by
      exact_mod_cast hdenominator
    apply mul_right_cancel₀
      hdenominatorReal
    calc
      _ = denominator ^ (degree + 1) *
          evalPower coefficients
            (((left : ℝ) + (width : ℝ) * u) /
              denominator) := hhom
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
            (((left : ℝ) + (width : ℝ) * u) /
              denominator)) := by
      ring
    _ = _ := by simpa using hpoly

private lemma blue_fit_bounds {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5)) :
    0 < backwardBlueUpperRound3Back1 z ∧
      backwardBlueUpperRound3Back1 z < 1 := by
  let u : ℝ := (1000 * z - 375) / 225
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hfit :
      backwardBlueUpperRound3Back1 z =
        
        (120354440921269 / 409600000000000) * (1 - u) ^ 4 +
          (654796662705413 / 512000000000000) * u * (1 - u) ^ 3 +
          (3275028874557231 / 1600000000000000) * u ^ 2 * (1 - u) ^ 2 +
          (1438907404021507 / 1000000000000000) * u ^ 3 * (1 - u) +
          (235109531468071 / 625000000000000) * u ^ 4 := by
    dsimp [u, backwardBlueUpperRound3Back1]
    ring
  have hone :
      1 - backwardBlueUpperRound3Back1 z =
        
        (289245559078731 / 409600000000000) * (1 - u) ^ 4 +
          (1393203337294587 / 512000000000000) * u * (1 - u) ^ 3 +
          (6324971125442769 / 1600000000000000) * u ^ 2 * (1 - u) ^ 2 +
          (2561092595978493 / 1000000000000000) * u ^ 3 * (1 - u) +
          (389890468531929 / 625000000000000) * u ^ 4 := by
    dsimp [u, backwardBlueUpperRound3Back1]
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
    (hz : z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5)) :
    backwardBlueRawUpper (3 / 100) z ≤
      backwardBlueUpperRound3Back1 z := by
  let u : ℝ := (1000 * z - 375) / 225
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hsum := bernstein_sum_pos_of_ends 49
    blueBernsteinCoeffs hu (by
      norm_num [blueBernsteinCoeffs, decimalNat]) (by
      norm_num [blueBernsteinCoeffs, decimalNat])
  have hpower := evalPower_eq_bernstein_of_identity
    49 1000 375 225 blueIdentityScale
    bluePowerCoeffs blueBernsteinCoeffs
    (by norm_num) (by
      norm_num [blueIdentityScale, decimalNat])
    (by norm_num [bluePowerCoeffs])
    blue_polynomial_identity u
  have hzFromU :
      ((375 + 225 * u) / 1000 : ℝ) = z := by
    dsimp [u]
    ring
  norm_num at hpower
  rw [hzFromU] at hpower
  have hzplus : 0 < 1 + z := by
    nlinarith [hz.1]
  have hrat :
      backwardBlueUpperRound3Back1 z -
          backwardBlueRawUpper (3 / 100) z =
        (evalPower bluePowerCoeffs z / bluePowerScale) /
          (1 + z) := by
    dsimp [backwardBlueRawUpper, backwardExpQUpper,
      backwardQUpper, mediumCorrectionPolynomial,
      backwardBlueUpperRound3Back1]
    norm_num [KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Finset.sum_range_succ,
      Nat.factorial]
    dsimp [evalPower, bluePowerCoeffs, bluePowerScale,
      decimalNat]
    field_simp [hzplus.ne']
    ring
  rw [← sub_nonneg, hrat, hpower]
  have hIdentityScale : (0 : ℝ) < blueIdentityScale := by
    norm_num [blueIdentityScale, decimalNat]
  have hPowerScale : (0 : ℝ) < bluePowerScale := by
    norm_num [bluePowerScale, decimalNat]
  positivity

private lemma backward_book_lower_pos {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5)) :
    0 < backwardBookLowerTwo (33 / 1000) (3 / 100)
      (r3Back1TReal z) (backwardBlueUpperRound3Back1 z) z := by
  let u : ℝ := (1000 * z - 375) / 225
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hpower : 0 < evalIntegerPower bookPowerCoeffs u := by
    by_cases hleft : u ≤ 1 / 2
    · have huInterval :
          u ∈
            ({ lo := 0, hi := 1 / 2, le := by norm_num } :
              LeanCert.Core.IntervalRat) := by
        simpa [LeanCert.Core.IntervalRat.mem_def] using
          And.intro hu.1 hleft
      exact eval_integer_power_pos_of_interval bookPowerCoeffs
        ({ lo := 0, hi := 1 / 2, le := by norm_num } :
          LeanCert.Core.IntervalRat)
        huInterval book_horner_lower_left
    · let v : ℝ := 1 - u
      have hvInterval :
          v ∈
            ({ lo := 0, hi := 1 / 2, le := by norm_num } :
              LeanCert.Core.IntervalRat) := by
        have hv : v ∈ Set.Icc (0 : ℝ) (1 / 2) := by
          dsimp [v]
          constructor <;> nlinarith [hu.2]
        simpa [LeanCert.Core.IntervalRat.mem_def] using hv
      have hreflected :
          0 < evalIntegerPower bookReflectedCoeffs v :=
        eval_integer_power_pos_of_interval bookReflectedCoeffs
          ({ lo := 0, hi := 1 / 2, le := by norm_num } :
            LeanCert.Core.IntervalRat)
          hvInterval book_horner_lower_right_reflected
      rw [book_reflected_eval] at hreflected
      simpa [v] using hreflected
  obtain ⟨hB0, hB1⟩ := blue_fit_bounds hz
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  obtain ⟨_, hM0, hM1⟩ :=
    backward_mu_upper_nine_bounds hzunit
  have hzplus2 : 0 < z + 2 := by
    nlinarith [hz.1]
  have hBsub1 : 0 < 1 - backwardBlueUpperRound3Back1 z :=
    sub_pos.mpr hB1
  have hBsub2 : 0 < 2 - backwardBlueUpperRound3Back1 z := by
    linarith
  have hMsub1 : 0 < 1 - backwardMuUpperNine z :=
    sub_pos.mpr hM1
  have hMsub2 : 0 < 2 - backwardMuUpperNine z := by
    linarith
  have hAffinePoint :
      ((375 : ℝ) + 225 * u) / 1000 = z := by
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
            (33 / 1000) (3 / 100) bookTPower bookBluePower) z := by
    rw [book_numerator_eval]
    exact hNumeratorExpanded
  have htEval :
      rationalPowerEval bookTPower z = r3Back1TReal z := by
    rw [bookTPower, rationalPowerEval_comp]
    norm_num [rationalPowerEval, r3Back1TReal,
      tangentLocalPoly, tangentRatHorner,
      TangentAffine.r3Back1Cs]
    ring
  have hblueEval :
      rationalPowerEval bookBluePower z =
        backwardBlueUpperRound3Back1 z := by
    norm_num [bookBluePower, rationalPowerEval,
      backwardBlueUpperRound3Back1]
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
      (33 / 1000) (3 / 100) bookTPower bookBluePower z
      hzplus2.ne' hBPowerSub1.ne' hBPowerSub2.ne'
      hMsub1.ne' hMsub2.ne'
  rw [htEval, hblueEval] at hBridge
  have hClosedCast :
      0 <
        backwardBookLowerTwoClosed
          ((33 / 1000 : ℚ) : ℝ) ((3 / 100 : ℚ) : ℝ)
          (r3Back1TReal z)
          (backwardBlueUpperRound3Back1 z) z := by
    rw [← hBridge]
    exact div_pos hNumerator hDenominator
  norm_num at hClosedCast
  have hClosed :
      0 <
        backwardBookLowerTwoClosed
          (33 / 1000) (3 / 100) (r3Back1TReal z)
          (backwardBlueUpperRound3Back1 z) z :=
    hClosedCast
  rw [backwardBookLowerTwo_eq_closed
    (33 / 1000) (3 / 100) (r3Back1TReal z)
    (backwardBlueUpperRound3Back1 z) z
    hB0.le hB1 hM0 hM1]
  exact hClosed

/-- The book inequality on the round-3 backward-1 interval. -/
lemma tangent_backward_book_round3_back1 :
    ∀ z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5),
      0 < tangentCleanBookMargin (3 / 100) z
        (tangentALog (33 / 1000) (r3Back1TReal z) -
          Real.log z) := by
  intro z hz
  obtain ⟨ht0, ht1⟩ :=
    BackwardCoordRound3Back1Bounds.round3_back1_t_bounds hz
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  obtain ⟨hB0, hB1⟩ := blue_fit_bounds hz
  have hblueRaw := raw_blue_le_fit hz
  have hblue := (tangent_blue_le_backward_raw_upper
    (β := (3 / 100 : ℝ)) (z := z) (by norm_num)
    hzunit).trans hblueRaw
  exact (backward_book_lower_pos hz).trans_le
    (backward_book_lower_two_le
      (by norm_num) (by norm_num) hzunit
      (by nlinarith [hz.1])
      ⟨ht0.le, ht1.le⟩ hB0.le hblue hB1)

end

end BackwardBookRound3Back1Bounds
end Arxiv2407_19026
