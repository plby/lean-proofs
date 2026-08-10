import Arxiv.Arxiv2407_19026.TangentChecks2Front
import Arxiv.Arxiv2407_19026.TangentCertifiedRound1
import Arxiv.Arxiv2407_19026.TangentPlateauBookRound2Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back1Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound2Back1Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound2Back2Bounds

noncomputable section

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026

private lemma r2_smallCoordPrime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 10),
      (1 / 20 : ℝ) ≤
        tangentSmallCoordLogPrime (9 / 200) (33 / 1000) z := by
  exact TangentRound2Native.small_coord_lower

private lemma r2_smallBookPrime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 50),
      (1 / 1000 : ℝ) ≤
        tangentSmallBookMarginPrime (9 / 200) (33 / 1000) z := by
  exact TangentRound2Native.small_book_prime_lower

private lemma r2_smallBook_lower :
    ∀ z ∈ Set.Icc (1 / 50 : ℝ) (1 / 10),
      (1 / 10000 : ℝ) ≤
        tangentSmallBookMargin (9 / 200) (33 / 1000) z := by
  exact TangentRound2Native.small_book_lower

private lemma r2_forwardCoord :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      tangentXLog (33 / 1000) z ≤
        tangentALog (9 / 200) (r2ForwardTReal z) := by
  exact ForwardCoordRound2Bounds.tangent_forward_coord_round2

private lemma r2_forwardBook :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      0 < tangentCleanBookMargin (33 / 1000) z
        (tangentBLog (9 / 200) (r2ForwardTReal z) - Real.log z) := by
  exact ForwardRound2Bounds.tangent_forward_book_round2

private lemma r2_plateauLow :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (189 / 500),
      tangentBLog (9 / 200) (99 / 100) ≤ tangentXLog (33 / 1000) z := by
  exact TangentRound2Native.plateau_low_lower

private lemma r2_plateauHigh :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (189 / 500),
      tangentXLog (33 / 1000) z ≤ tangentALog (9 / 200) (99 / 100) := by
  exact TangentRound2Native.plateau_high_lower

private lemma r2_plateauBook :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (189 / 500),
      0 < tangentCleanBookMargin (33 / 1000) z
        (tangentALog (9 / 200) (99 / 100) +
          tangentBLog (9 / 200) (99 / 100) -
          tangentXLog (33 / 1000) z - Real.log z) := by
  simpa only [show (67 / 250 : ℝ) = 268 / 1000 by norm_num] using
    PlateauBookRound2Bounds.tangent_plateau_book_round2

private lemma r2_back1Coord :
    ∀ z ∈ Set.Icc (189 / 500 : ℝ) (3 / 5),
      tangentXLog (33 / 1000) z ≤
        tangentBLog (9 / 200) (r2Back1TReal z) := by
  exact
    BackwardCoordRound2Back1Bounds.tangent_backward_coord_round2_back1

private lemma r2_back1Book :
    ∀ z ∈ Set.Icc (189 / 500 : ℝ) (3 / 5),
      0 < tangentCleanBookMargin (33 / 1000) z
        (tangentALog (9 / 200) (r2Back1TReal z) - Real.log z) := by
  exact
    BackwardBookRound2Back1Bounds.tangent_backward_book_round2_back1

private lemma r2_back2Coord :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      tangentXLog (33 / 1000) z ≤
        tangentBLog (9 / 200) (r2Back2TReal z) := by
  exact
    BackwardCoordRound2Back2Bounds.tangent_backward_coord_round2_back2

private lemma r2_back2Book :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      0 < tangentCleanBookMargin (33 / 1000) z
        (tangentALog (9 / 200) (r2Back2TReal z) - Real.log z) := by
  exact
    BackwardBookRound2Back2Bounds.tangent_backward_book_round2_back2

def tangentRoundWitnessData2 :
    TangentRoundWitnessData (9 / 200) (33 / 1000)
      (67 / 250) (189 / 500) where
  forwardT := r2ForwardTReal
  back1T := r2Back1TReal
  back2T := r2Back2TReal
  cut_order := by norm_num
  forwardT_mem := r2ForwardTReal_mem
  back1T_mem := r2Back1TReal_mem
  back2T_mem := r2Back2TReal_mem
  smallCoord :=
    tangentSmallCoord_pos_of_deriv_lower (by norm_num)
      r2_smallCoordPrime_lower
  smallBook :=
    tangentSmallBook_pos_of_bounds (by norm_num)
      r2_smallBookPrime_lower r2_smallBook_lower
  forwardCoord := r2_forwardCoord
  forwardBook := r2_forwardBook
  plateauLow := r2_plateauLow
  plateauHigh := r2_plateauHigh
  plateauBook := r2_plateauBook
  back1Coord := r2_back1Coord
  back1Book := r2_back1Book
  back2Coord := r2_back2Coord
  back2Book := r2_back2Book

theorem tangentRoundCertificate2 :
    TangentRoundCertificate (9 / 200) (33 / 1000) :=
  tangentRoundWitnessData2.toCertificate (by norm_num)

theorem hasRamseyExponent_beta2 :
    HasRamseyExponent (optimizedRamseyExponent (33 / 1000)) :=
  hasRamseyExponent_of_tangentRoundCertificate
    (by norm_num) (by norm_num) (by norm_num)
    hasRamseyExponent_beta1 tangentRoundCertificate2

end Arxiv2407_19026
