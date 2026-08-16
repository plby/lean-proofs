import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back2BlueBounds
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back2ScaledSemantics
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound1Back2Bounds

/-!
# First-round second backward book bound

This file combines the cached blue-fit and book-margin certificates with the
analytic comparison lemmas on `[0.6, 1.0]`.
-/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back2Bounds

noncomputable section

open BackwardBookRound1Back2Certificate

private lemma backward_book_lower_pos {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 5 : ℝ) 1) :
    0 < backwardBookLowerTwo (2 / 25) (9 / 200)
      (r1Back2TReal z) (backwardBlueUpperRound1Back2 z) z := by
  let u : ℝ := (1000 * z - 600) / 400
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
  have hBsub1 : 0 < 1 - backwardBlueUpperRound1Back2 z :=
    sub_pos.mpr hB1
  have hBsub2 : 0 < 2 - backwardBlueUpperRound1Back2 z := by
    linarith
  have hMsub1 : 0 < 1 - backwardMuUpperNine z :=
    sub_pos.mpr hM1
  have hMsub2 : 0 < 2 - backwardMuUpperNine z := by
    linarith
  have hAffinePoint :
      ((600 : ℝ) + 400 * u) / 1000 = z := by
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
  have hNumerator :
      0 <
        rationalPowerEval
          (backwardBookNumeratorTwoPower
            (2 / 25) (9 / 200) bookTPower bookBluePower) z := by
    rw [book_numerator_scaled_eval]
    apply div_pos hNumeratorInteger
    norm_num [bookNumeratorScale, decimalNat]
  have htEval :
      rationalPowerEval bookTPower z = r1Back2TReal z := by
    rw [bookTPower, rationalPowerEval_comp]
    norm_num [rationalPowerEval, r1Back2TReal,
      tangentLocalPoly, tangentRatHorner,
      TangentAffine.r1Back2Cs]
    ring
  have hblueEval :
      rationalPowerEval bookBluePower z =
        backwardBlueUpperRound1Back2 z := by
    norm_num [bookBluePower, rationalPowerEval,
      backwardBlueUpperRound1Back2]
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
          (r1Back2TReal z)
          (backwardBlueUpperRound1Back2 z) z := by
    rw [← hBridge]
    exact div_pos hNumerator hDenominator
  norm_num at hClosedCast
  have hClosed :
      0 <
        backwardBookLowerTwoClosed
          (2 / 25) (9 / 200) (r1Back2TReal z)
          (backwardBlueUpperRound1Back2 z) z :=
    hClosedCast
  rw [backwardBookLowerTwo_eq_closed
    (2 / 25) (9 / 200) (r1Back2TReal z)
    (backwardBlueUpperRound1Back2 z) z
    hB0.le hB1 hM0 hM1]
  exact hClosed

/-- The book inequality on the round-1 backward-2 interval. -/
lemma tangent_backward_book_round1_back2 :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      0 < tangentCleanBookMargin (9 / 200) z
        (tangentALog (2 / 25) (r1Back2TReal z) -
          Real.log z) := by
  intro z hz
  obtain ⟨ht0, ht1⟩ :=
    BackwardCoordRound1Back2Bounds.round1_back2_t_bounds hz
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
      ⟨ht0.le, by nlinarith [ht1]⟩ hB0.le hblue hB1)

end

end BackwardBookRound1Back2Bounds
end Arxiv2407_19026
