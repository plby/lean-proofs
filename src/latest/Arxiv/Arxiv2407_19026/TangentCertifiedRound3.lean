import Arxiv.Arxiv2407_19026.TangentChecks3Front
import Arxiv.Arxiv2407_19026.TangentChecks3.Defs
import Arxiv.Arxiv2407_19026.TangentCertifiedRound2
import Arxiv.Arxiv2407_19026.TangentForwardCoordRound3Bounds
import Arxiv.Arxiv2407_19026.TangentForwardRound3Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back1Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound3Back1Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound3Back2Bounds

noncomputable section

namespace Arxiv2407_19026

private lemma r3PlateauMedium_ne :
    TangentRound3Native.plateauMedium ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 268 107 (by norm_num)

private lemma r3PlateauMedium_last :
    TangentRound3Native.plateauMedium.getLast r3PlateauMedium_ne =
      3 / 8 := by
  unfold TangentRound3Native.plateauMedium
  convert TangentAffine.mediumBreakpoints_getLast
    268 107 (by norm_num) r3PlateauMedium_ne using 1
  all_goals norm_num

private lemma r3_smallCoordPrime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 10),
      (1 / 20 : ℝ) ≤
        tangentSmallCoordLogPrime (33 / 1000) (3 / 100) z := by
  exact TangentRound3Native.small_coord_lower

private lemma r3_smallBookPrime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 50),
      (1 / 1000 : ℝ) ≤
        tangentSmallBookMarginPrime (33 / 1000) (3 / 100) z := by
  exact TangentRound3Native.small_book_prime_lower

private lemma r3_smallBook_lower :
    ∀ z ∈ Set.Icc (1 / 50 : ℝ) (1 / 10),
      (1 / 10000 : ℝ) ≤
        tangentSmallBookMargin (33 / 1000) (3 / 100) z := by
  exact TangentRound3Native.small_book_lower

private lemma r3_forwardCoord :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      tangentXLog (3 / 100) z ≤
        tangentALog (33 / 1000) (r3ForwardTReal z) := by
  exact ForwardCoordRound3Bounds.tangent_forward_coord_round3

private lemma r3_forwardBook :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      0 < tangentCleanBookMargin (3 / 100) z
        (tangentBLog (33 / 1000) (r3ForwardTReal z) - Real.log z) := by
  exact ForwardRound3Bounds.tangent_forward_book_round3

private lemma r3_plateauLow :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (3 / 8),
      tangentBLog (33 / 1000) (99 / 100) ≤ tangentXLog (3 / 100) z := by
  exact TangentRound3Native.plateau_low_lower

private lemma r3_plateauHigh :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (3 / 8),
      tangentXLog (3 / 100) z ≤ tangentALog (33 / 1000) (99 / 100) := by
  exact TangentRound3Native.plateau_high_lower

private lemma r3_plateauBook :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (3 / 8),
      0 < tangentCleanBookMargin (3 / 100) z
        (tangentALog (33 / 1000) (99 / 100) +
          tangentBLog (33 / 1000) (99 / 100) -
          tangentXLog (3 / 100) z - Real.log z) := by
  exact TangentRound3Native.plateau_book_lower

private lemma r3_back1Coord :
    ∀ z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5),
      tangentXLog (3 / 100) z ≤
        tangentBLog (33 / 1000) (r3Back1TReal z) := by
  exact
    BackwardCoordRound3Back1Bounds.tangent_backward_coord_round3_back1

private lemma r3_back1Book :
    ∀ z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5),
      0 < tangentCleanBookMargin (3 / 100) z
        (tangentALog (33 / 1000) (r3Back1TReal z) - Real.log z) := by
  exact
    BackwardBookRound3Back1Bounds.tangent_backward_book_round3_back1

private lemma r3_back2Coord :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      tangentXLog (3 / 100) z ≤
        tangentBLog (33 / 1000) (r3Back2TReal z) := by
  exact
    BackwardCoordRound3Back2Bounds.tangent_backward_coord_round3_back2

private lemma r3_back2Book :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      0 < tangentCleanBookMargin (3 / 100) z
        (tangentALog (33 / 1000) (r3Back2TReal z) - Real.log z) := by
  exact
    BackwardBookRound3Back2Bounds.tangent_backward_book_round3_back2

def tangentRoundWitnessData3 :
    TangentRoundWitnessData (33 / 1000) (3 / 100)
      (67 / 250) (3 / 8) where
  forwardT := r3ForwardTReal
  back1T := r3Back1TReal
  back2T := r3Back2TReal
  cut_order := by norm_num
  forwardT_mem := r3ForwardTReal_mem
  back1T_mem := r3Back1TReal_mem
  back2T_mem := r3Back2TReal_mem
  smallCoord :=
    tangentSmallCoord_pos_of_deriv_lower (by norm_num)
      r3_smallCoordPrime_lower
  smallBook :=
    tangentSmallBook_pos_of_bounds (by norm_num)
      r3_smallBookPrime_lower r3_smallBook_lower
  forwardCoord := r3_forwardCoord
  forwardBook := r3_forwardBook
  plateauLow := r3_plateauLow
  plateauHigh := r3_plateauHigh
  plateauBook := r3_plateauBook
  back1Coord := r3_back1Coord
  back1Book := r3_back1Book
  back2Coord := r3_back2Coord
  back2Book := r3_back2Book

theorem tangentRoundCertificate3 :
    TangentRoundCertificate (33 / 1000) (3 / 100) :=
  tangentRoundWitnessData3.toCertificate (by norm_num)

theorem hasRamseyExponent_beta3 :
    HasRamseyExponent (optimizedRamseyExponent (3 / 100)) :=
  hasRamseyExponent_of_tangentRoundCertificate
    (by norm_num) (by norm_num) (by norm_num)
    hasRamseyExponent_beta2 tangentRoundCertificate3

end Arxiv2407_19026
