import Arxiv.Arxiv2407_19026.NumericalProfilesBook3StageData

/-! Staged exact coefficient proofs for the third profile book bound. -/

namespace Arxiv2407_19026
namespace NumericalProfilesBook3Certificate

noncomputable section

lemma book_three_v_power_expansion :
    bookThreeVPower = bookThreeVExpandedPower := by
  norm_num [bookThreeVPower, bookThreeVExpandedPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

lemma book_three_x_power_expansion :
    bookThreeXPower = bookThreeXExpandedPower := by
  rw [bookThreeXPower, book_three_v_power_expansion]
  norm_num [bookThreeVExpandedPower, bookThreeXExpandedPower,
    rationalPowerMul, rationalPowerShift, rationalPowerScale,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd]

lemma book_three_w_power_expansion :
    bookThreeWPower = bookThreeWExpandedPower := by
  rw [bookThreeWPower, book_three_v_power_expansion]
  norm_num [bookThreeVExpandedPower, bookThreeWExpandedPower,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd]

lemma book_three_exp_neg_upper_power_expansion :
    bookThreeExpNegUpperPower =
      bookThreeExpNegUpperExpandedPower := by
  norm_num [bookThreeExpNegUpperPower,
    bookThreeExpNegUpperExpandedPower]

lemma book_three_correction_power_expansion :
    bookThreeCorrectionPower =
      bookThreeCorrectionExpandedPower := by
  rw [bookThreeCorrectionPower,
    book_three_exp_neg_upper_power_expansion]
  norm_num [bookThreeExpNegUpperExpandedPower,
    bookThreeCorrectionExpandedPower,
    rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

lemma book_three_entropy_numerator_power_expansion :
    bookThreeEntropyNumeratorPower =
      bookThreeEntropyNumeratorExpandedPower := by
  norm_num [bookThreeEntropyNumeratorPower,
    bookThreeEntropyNumeratorExpandedPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

set_option maxHeartbeats 500000 in
-- Expanding the degree-70 below-one numerator exceeds the default budget.
lemma book_three_below_numerator_power_expansion :
    bookThreeBelowNumeratorPower =
      bookThreeBelowNumeratorExpandedPower := by
  rw [bookThreeBelowNumeratorPower,
    book_three_x_power_expansion]
  norm_num [decimalNat, bookThreeXExpandedPower,
    bookThreeBelowNumeratorExpandedPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerSub,
    rationalPowerNeg, rationalPowerAdd]

set_option maxHeartbeats 500000 in
-- Expanding the degree-45 near-one numerator exceeds the default budget.
lemma book_three_above_numerator_power_expansion :
    bookThreeAboveNumeratorPower =
      bookThreeAboveNumeratorExpandedPower := by
  rw [bookThreeAboveNumeratorPower,
    book_three_w_power_expansion]
  norm_num [decimalNat, bookThreeWExpandedPower,
    bookThreeAboveNumeratorExpandedPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerSub,
    rationalPowerNeg, rationalPowerAdd]

lemma book_three_b_one_power_expansion :
    bookThreeBOnePower = bookThreeBOneExpandedPower := by
  norm_num [bookThreeBOnePower, bookThreeBOneExpandedPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

set_option maxHeartbeats 500000 in
-- Expanding the degree-60 blue-coordinate denominator exceeds the default budget.
lemma book_three_bx_power_expansion :
    bookThreeBXPower = bookThreeBXExpandedPower := by
  rw [bookThreeBXPower, book_three_x_power_expansion]
  norm_num [decimalNat, bookThreeXExpandedPower,
    bookThreeBXExpandedPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

set_option maxHeartbeats 500000 in
-- Expanding the degree-36 loss-coordinate denominator exceeds the default budget.
lemma book_three_bv_power_expansion :
    bookThreeBVPower = bookThreeBVExpandedPower := by
  rw [bookThreeBVPower, book_three_w_power_expansion]
  norm_num [decimalNat, bookThreeWExpandedPower,
    bookThreeBVExpandedPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

set_option maxHeartbeats 1000000 in
-- Multiplying the staged entropy factors exceeds the default budget.
set_option maxRecDepth 5000 in
lemma book_three_entropy_term_power_expansion :
    bookThreeEntropyTermPower =
      bookThreeEntropyTermExpandedPower := by
  rw [bookThreeEntropyTermPower,
    book_three_entropy_numerator_power_expansion,
    book_three_bx_power_expansion,
    book_three_bv_power_expansion]
  norm_num [decimalNat, bookThreeEntropyNumeratorExpandedPower,
    bookThreeBXExpandedPower, bookThreeBVExpandedPower,
    bookThreeEntropyTermExpandedPower,
    rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

set_option maxHeartbeats 1000000 in
-- Multiplying the staged correction factors exceeds the default budget.
set_option maxRecDepth 5000 in
lemma book_three_correction_term_power_expansion :
    bookThreeCorrectionTermPower =
      bookThreeCorrectionTermExpandedPower := by
  rw [bookThreeCorrectionTermPower,
    book_three_correction_power_expansion,
    book_three_b_one_power_expansion,
    book_three_bx_power_expansion,
    book_three_bv_power_expansion]
  norm_num [decimalNat, bookThreeCorrectionExpandedPower,
    bookThreeBOneExpandedPower, bookThreeBXExpandedPower,
    bookThreeBVExpandedPower,
    bookThreeCorrectionTermExpandedPower,
    rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

set_option maxHeartbeats 1000000 in
-- Multiplying the staged below-one factors exceeds the default budget.
set_option maxRecDepth 5000 in
lemma book_three_below_term_power_expansion :
    bookThreeBelowTermPower =
      bookThreeBelowTermExpandedPower := by
  rw [bookThreeBelowTermPower,
    book_three_below_numerator_power_expansion,
    book_three_b_one_power_expansion,
    book_three_bv_power_expansion]
  norm_num [decimalNat, bookThreeBelowNumeratorExpandedPower,
    bookThreeBOneExpandedPower, bookThreeBVExpandedPower,
    bookThreeBelowTermExpandedPower,
    rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

set_option maxHeartbeats 1000000 in
-- Multiplying the staged quadratic-loss factors exceeds the default budget.
set_option maxRecDepth 5000 in
lemma book_three_z_square_term_power_expansion :
    bookThreeZSquareTermPower =
      bookThreeZSquareTermExpandedPower := by
  rw [bookThreeZSquareTermPower,
    book_three_b_one_power_expansion,
    book_three_bx_power_expansion,
    book_three_bv_power_expansion]
  norm_num [decimalNat, bookThreeBOneExpandedPower,
    bookThreeBXExpandedPower, bookThreeBVExpandedPower,
    bookThreeZSquareTermExpandedPower,
    rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerNeg,
    rationalPowerAdd]

set_option maxHeartbeats 1000000 in
-- Multiplying the staged near-one factors exceeds the default budget.
set_option maxRecDepth 5000 in
lemma book_three_above_term_power_expansion :
    bookThreeAboveTermPower =
      bookThreeAboveTermExpandedPower := by
  rw [bookThreeAboveTermPower,
    book_three_above_numerator_power_expansion,
    book_three_b_one_power_expansion,
    book_three_bx_power_expansion]
  norm_num [decimalNat, bookThreeAboveNumeratorExpandedPower,
    bookThreeBOneExpandedPower, bookThreeBXExpandedPower,
    bookThreeAboveTermExpandedPower,
    rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

set_option maxHeartbeats 1000000 in
-- Combining the five degree-116 staged terms exceeds the default budget.
set_option maxRecDepth 5000 in
lemma book_three_cleared_power_expansion :
    bookThreeClearedPower =
      bookThreeClearedExpandedPower := by
  rw [bookThreeClearedPower,
    book_three_entropy_term_power_expansion,
    book_three_correction_term_power_expansion,
    book_three_below_term_power_expansion,
    book_three_z_square_term_power_expansion,
    book_three_above_term_power_expansion]
  norm_num [bookThreeEntropyTermExpandedPower,
    bookThreeCorrectionTermExpandedPower,
    bookThreeBelowTermExpandedPower,
    bookThreeZSquareTermExpandedPower,
    bookThreeAboveTermExpandedPower,
    bookThreeClearedExpandedPower, decimalNat,
    rationalPowerScale, rationalPowerAdd]

set_option maxRecDepth 5000 in
lemma book_three_cleared_power_integer :
    bookThreeClearedPower =
      rationalPowerFromIntegers 1 bookThreePowerCoeffs := by
  rw [book_three_cleared_power_expansion]
  norm_num [bookThreeClearedExpandedPower,
    rationalPowerFromIntegers, bookThreePowerCoeffs,
    decimalNat]


end


end NumericalProfilesBook3Certificate
end Arxiv2407_19026
