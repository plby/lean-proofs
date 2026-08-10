import Arxiv.Arxiv2407_19026.TangentChecks1Front
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back1Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back2Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound1Back1Bounds
import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound1Back2Bounds
import Arxiv.Arxiv2407_19026.TangentForwardCoordRound1Bounds
import Arxiv.Arxiv2407_19026.TangentForwardRound1Bounds
import Arxiv.Arxiv2407_19026.TangentPlateauBookRound1Bounds
import Arxiv.Arxiv2407_19026.TangentVerified

noncomputable section

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026

private lemma r1_smallCoordPrime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 10),
      (1 / 20 : ℝ) ≤
        tangentSmallCoordLogPrime (2 / 25) (9 / 200) z := by
  exact TangentRound1Native.small_coord_lower

private lemma r1_smallBookPrime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 50),
      (1 / 1000 : ℝ) ≤
        tangentSmallBookMarginPrime (2 / 25) (9 / 200) z := by
  exact TangentRound1Native.small_book_prime_lower

private lemma r1_smallBook_lower :
    ∀ z ∈ Set.Icc (1 / 50 : ℝ) (1 / 10),
      (1 / 10000 : ℝ) ≤
        tangentSmallBookMargin (2 / 25) (9 / 200) z := by
  exact TangentRound1Native.small_book_lower

private lemma r1_forwardCoord :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (269 / 1000),
      tangentXLog (9 / 200) z ≤
        tangentALog (2 / 25) (r1ForwardTReal z) := by
  exact ForwardCoordRound1Bounds.tangent_forward_coord_round1

private lemma r1_forwardBook :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (269 / 1000),
      0 < tangentCleanBookMargin (9 / 200) z
        (tangentBLog (2 / 25) (r1ForwardTReal z) - Real.log z) := by
  exact ForwardRound1Bounds.tangent_forward_book_round1

private lemma r1_plateauLow :
    ∀ z ∈ Set.Icc (269 / 1000 : ℝ) (387 / 1000),
      tangentBLog (2 / 25) (99 / 100) ≤ tangentXLog (9 / 200) z := by
  exact TangentRound1Native.plateau_low_lower

private lemma r1_plateauHigh :
    ∀ z ∈ Set.Icc (269 / 1000 : ℝ) (387 / 1000),
      tangentXLog (9 / 200) z ≤ tangentALog (2 / 25) (99 / 100) := by
  exact TangentRound1Native.plateau_high_lower

private lemma r1_plateauBook :
    ∀ z ∈ Set.Icc (269 / 1000 : ℝ) (387 / 1000),
      0 < tangentCleanBookMargin (9 / 200) z
        (tangentALog (2 / 25) (99 / 100) +
          tangentBLog (2 / 25) (99 / 100) -
          tangentXLog (9 / 200) z - Real.log z) := by
  exact PlateauBookRound1Bounds.tangent_plateau_book_round1

private lemma r1_back1Coord :
    ∀ z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5),
      tangentXLog (9 / 200) z ≤
        tangentBLog (2 / 25) (r1Back1TReal z) := by
  exact
    BackwardCoordRound1Back1Bounds.tangent_backward_coord_round1_back1

private lemma r1_back1Book :
    ∀ z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5),
      0 < tangentCleanBookMargin (9 / 200) z
        (tangentALog (2 / 25) (r1Back1TReal z) - Real.log z) := by
  exact
    BackwardBookRound1Back1Bounds.tangent_backward_book_round1_back1

private lemma r1_back2Coord :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      tangentXLog (9 / 200) z ≤
        tangentBLog (2 / 25) (r1Back2TReal z) := by
  exact
    BackwardCoordRound1Back2Bounds.tangent_backward_coord_round1_back2

private lemma r1_back2Book :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      0 < tangentCleanBookMargin (9 / 200) z
        (tangentALog (2 / 25) (r1Back2TReal z) - Real.log z) := by
  exact
    BackwardBookRound1Back2Bounds.tangent_backward_book_round1_back2

def tangentRoundWitnessData1 :
    TangentRoundWitnessData (2 / 25) (9 / 200)
      (269 / 1000) (387 / 1000) where
  forwardT := r1ForwardTReal
  back1T := r1Back1TReal
  back2T := r1Back2TReal
  cut_order := by norm_num
  forwardT_mem := r1ForwardTReal_mem
  back1T_mem := r1Back1TReal_mem
  back2T_mem := r1Back2TReal_mem
  smallCoord :=
    tangentSmallCoord_pos_of_deriv_lower (by norm_num)
      r1_smallCoordPrime_lower
  smallBook :=
    tangentSmallBook_pos_of_bounds (by norm_num)
      r1_smallBookPrime_lower r1_smallBook_lower
  forwardCoord := r1_forwardCoord
  forwardBook := r1_forwardBook
  plateauLow := r1_plateauLow
  plateauHigh := r1_plateauHigh
  plateauBook := r1_plateauBook
  back1Coord := r1_back1Coord
  back1Book := r1_back1Book
  back2Coord := r1_back2Coord
  back2Book := r1_back2Book

theorem tangentRoundCertificate1 :
    TangentRoundCertificate (2 / 25) (9 / 200) :=
  tangentRoundWitnessData1.toCertificate (by norm_num)

theorem hasRamseyExponent_beta1 :
    HasRamseyExponent (optimizedRamseyExponent (9 / 200)) :=
  hasRamseyExponent_of_tangentRoundCertificate
    (by norm_num) (by norm_num) (by norm_num)
    hasRamseyExponent_beta0 tangentRoundCertificate1

end Arxiv2407_19026
