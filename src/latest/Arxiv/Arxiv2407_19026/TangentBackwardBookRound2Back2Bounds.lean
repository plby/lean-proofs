import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back2BlueBounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound2Back2Bounds

/-!
# Second-round second backward book bound

This file combines the cached blue-fit and book-margin certificates with the
analytic comparison lemmas on `[0.6, 1.0]`.
-/

namespace Arxiv2407_19026
namespace BackwardBookRound2Back2Bounds

noncomputable section

open BackwardBookRound2Back2Certificate

private lemma backward_book_lower_pos {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 5 : ℝ) 1) :
    0 < backwardBookLowerThree (9 / 200) (33 / 1000)
      (r2Back2TReal z) (backwardBlueUpperRound2Back2 z) z := by
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
  obtain ⟨_, _, hM1⟩ :=
    backward_mu_upper_nine_bounds hzunit
  have hzplus2 : 0 < z + 2 := by
    nlinarith [hz.1]
  have hBsub1 : 0 < 1 - backwardBlueUpperRound2Back2 z :=
    sub_pos.mpr hB1
  have hBsub2 : 0 < 2 - backwardBlueUpperRound2Back2 z := by
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
  have hNumeratorExpanded :
      0 < rationalPowerEval bookNumeratorExpandedPower z := by
    rw [book_numerator_integer_eval]
    apply div_pos hNumeratorInteger
    norm_num [bookNumeratorScale, decimalNat]
  have hNumerator :
      0 <
        rationalPowerEval
          (backwardBookNumeratorThreePower
            (9 / 200) (33 / 1000) bookTPower bookBluePower) z := by
    rw [book_numerator_eval]
    exact hNumeratorExpanded
  have htEval :
      rationalPowerEval bookTPower z = r2Back2TReal z := by
    rw [bookTPower, rationalPowerEval_comp]
    norm_num [rationalPowerEval, r2Back2TReal,
      tangentLocalPoly, tangentRatHorner,
      TangentAffine.r2Back2Cs]
    ring
  have hblueEval :
      rationalPowerEval bookBluePower z =
        backwardBlueUpperRound2Back2 z := by
    norm_num [bookBluePower, rationalPowerEval,
      backwardBlueUpperRound2Back2]
    ring
  have hDenominator :
      0 <
        rationalPowerEval
          (backwardBookDenominatorThreePower bookBluePower) z := by
    rw [backwardBookDenominatorThreePower,
      rationalPowerEval_mul]
    apply mul_pos
    · rw [backwardEntropyDenominatorPower_eval]
      exact pow_pos hzplus2 9
    · rw [rationalPowerEval_mul]
      apply mul_pos
      · rw [backwardLogThreeDenominatorPower_eval,
          hblueEval]
        exact mul_pos
          (mul_pos (by norm_num) hBsub1)
          (pow_pos hBsub2 5)
      · rw [backwardLogThreeDenominatorPower_eval,
          backwardMuPower_eval]
        exact mul_pos
          (mul_pos (by norm_num) hMsub1)
          (pow_pos hMsub2 5)
  have hBPowerSub1 :
      0 < 1 - rationalPowerEval bookBluePower z := by
    rw [hblueEval]
    exact hBsub1
  have hBPowerSub2 :
      0 < 2 - rationalPowerEval bookBluePower z := by
    rw [hblueEval]
    exact hBsub2
  have hBridge :=
    backwardBookNumeratorThreePower_eval_closed
      (9 / 200) (33 / 1000) bookTPower bookBluePower z
      hzplus2.ne' hBPowerSub1.ne' hBPowerSub2.ne'
      hMsub1.ne' hMsub2.ne'
  rw [htEval, hblueEval] at hBridge
  have hClosedCast :
      0 <
        backwardBookLowerThreeClosed
          ((9 / 200 : ℚ) : ℝ) ((33 / 1000 : ℚ) : ℝ)
          (r2Back2TReal z)
          (backwardBlueUpperRound2Back2 z) z := by
    rw [← hBridge]
    exact div_pos hNumerator hDenominator
  norm_num at hClosedCast
  have hClosed :
      0 <
        backwardBookLowerThreeClosed
          (9 / 200) (33 / 1000) (r2Back2TReal z)
          (backwardBlueUpperRound2Back2 z) z :=
    hClosedCast
  rw [backwardBookLowerThree_eq_closed
    (9 / 200) (33 / 1000) (r2Back2TReal z)
    (backwardBlueUpperRound2Back2 z) z
    hB1 hM1]
  exact hClosed

/-- The book inequality on the round-2 backward-2 interval. -/
lemma tangent_backward_book_round2_back2 :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      0 < tangentCleanBookMargin (33 / 1000) z
        (tangentALog (9 / 200) (r2Back2TReal z) -
          Real.log z) := by
  intro z hz
  obtain ⟨ht0, ht1⟩ :=
    BackwardCoordRound2Back2Bounds.round2_back2_t_bounds hz
  have hzunit : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  obtain ⟨hB0, hB1⟩ := blue_fit_bounds hz
  have hblueRaw := raw_blue_le_fit hz
  have hblue := (tangent_blue_le_backward_raw_upper
    (β := (33 / 1000 : ℝ)) (z := z) (by norm_num)
    hzunit).trans hblueRaw
  exact (backward_book_lower_pos hz).trans_le
    (backward_book_lower_three_le
      (by norm_num) (by norm_num) hzunit
      (by nlinarith [hz.1])
      ⟨ht0.le, by nlinarith [ht1]⟩ hB0.le hblue hB1)

end

end BackwardBookRound2Back2Bounds
end Arxiv2407_19026
