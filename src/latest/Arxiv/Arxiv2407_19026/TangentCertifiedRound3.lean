import Arxiv.Arxiv2407_19026.TangentChecks3Front
import Arxiv.Arxiv2407_19026.TangentCertifiedRound2

noncomputable section

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026

private lemma r3_smallCoordPrime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 10),
      (1 / 20 : ℝ) ≤
        tangentSmallCoordLogPrime (33 / 1000) (3 / 100) z := by
  have h := affineLowerEval
    (TangentAffine.smallCoordSlope
      TangentRound3Native.β2 TangentRound3Native.β3)
    (1 / 20) 0 (1 / 10)
    TangentRound3Native.smallCoordRefined
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound3Native.small_checks.1
  intro z hz
  have hd := tangentSmall_domain
    (β := (TangentRound3Native.β3 : ℝ))
    (by norm_num [TangentRound3Native.β3]) hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_smallCoordSlope _ _ _
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2] at hh
  norm_num [TangentRound3Native.β2, TangentRound3Native.β3] at hh
  exact hh

private lemma r3_smallBookPrime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 50),
      (1 / 1000 : ℝ) ≤
        tangentSmallBookMarginPrime (33 / 1000) (3 / 100) z := by
  have h := affineLowerEval
    (TangentAffine.smallBookSlope
      TangentRound3Native.β2 TangentRound3Native.β3)
    (1 / 1000) 0 (1 / 50) TangentAffine.bpsBookSlope
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound3Native.small_checks.2.1
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) (1 / 10) := by
    constructor
    · exact hz.1
    · nlinarith [hz.2]
  have hd := tangentSmall_domain
    (β := (TangentRound3Native.β3 : ℝ))
    (by norm_num [TangentRound3Native.β3]) hz'
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_smallBookSlope _ _ _
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2] at hh
  norm_num [TangentRound3Native.β2, TangentRound3Native.β3] at hh
  exact hh

private lemma r3_smallBook_lower :
    ∀ z ∈ Set.Icc (1 / 50 : ℝ) (1 / 10),
      (1 / 10000 : ℝ) ≤
        tangentSmallBookMargin (33 / 1000) (3 / 100) z := by
  have h := affineLowerEval
    (TangentAffine.smallBook
      TangentRound3Native.β2 TangentRound3Native.β3)
    (1 / 10000) (1 / 50) (1 / 10) TangentAffine.bpsBook
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound3Native.small_checks.2.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_smallBook] at hh
  norm_num [TangentRound3Native.β2, TangentRound3Native.β3] at hh
  exact hh

private lemma r3_forwardCoord :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      tangentXLog (3 / 100) z ≤
        tangentALog (33 / 1000) (r3ForwardTReal z) := by
  have h := affineLowerEval
    (TangentAffine.forwardLogCoord
      TangentRound3Native.β2 TangentRound3Native.β3
      TangentAffine.r3ForwardT)
    0 (1 / 10) (67 / 250)
    TangentRound3Native.forwardCoordRefined
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound3Native.forward_checks.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_forwardLogCoord, eval_r3ForwardT] at hh
  norm_num [TangentRound3Native.β2, TangentRound3Native.β3] at hh
  linarith

private lemma r3_forwardBook :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      0 < tangentCleanBookMargin (3 / 100) z
        (tangentBLog (33 / 1000) (r3ForwardTReal z) - Real.log z) := by
  have h := affineLowerEval
    (TangentAffine.forwardBook
      TangentRound3Native.β2 TangentRound3Native.β3
      TangentAffine.r3ForwardT)
    (1 / 1000000) (1 / 10) (67 / 250)
    TangentRound3Native.forwardMedium
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound3Native.forward_checks.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_forwardBook, eval_r3ForwardT] at hh
  norm_num [TangentRound3Native.β2, TangentRound3Native.β3] at hh
  positivity

private lemma r3_plateauLow :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (3 / 8),
      tangentBLog (33 / 1000) (99 / 100) ≤ tangentXLog (3 / 100) z := by
  have h := affineLowerEval
    (TangentAffine.plateauLogLow
      TangentRound3Native.β2 TangentRound3Native.β3
      TangentRound3Native.plateauT)
    0 (67 / 250) (3 / 8)
    TangentRound3Native.plateauMedium
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound3Native.plateau_checks.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_plateauLogLow] at hh
  norm_num [TangentRound3Native.β2, TangentRound3Native.β3,
    TangentRound3Native.plateauT, TangentAffine.c, Expr.eval] at hh
  linarith

private lemma r3_plateauHigh :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (3 / 8),
      tangentXLog (3 / 100) z ≤ tangentALog (33 / 1000) (99 / 100) := by
  have h := affineLowerEval
    (TangentAffine.plateauLogHigh
      TangentRound3Native.β2 TangentRound3Native.β3
      TangentRound3Native.plateauT)
    0 (67 / 250) (3 / 8)
    TangentRound3Native.plateauMedium
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound3Native.plateau_checks.2.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_plateauLogHigh] at hh
  norm_num [TangentRound3Native.β2, TangentRound3Native.β3,
    TangentRound3Native.plateauT, TangentAffine.c, Expr.eval] at hh
  linarith

private lemma r3_plateauBook :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (3 / 8),
      0 < tangentCleanBookMargin (3 / 100) z
        (tangentALog (33 / 1000) (99 / 100) +
          tangentBLog (33 / 1000) (99 / 100) -
          tangentXLog (3 / 100) z - Real.log z) := by
  have h := affineLowerEval
    (TangentAffine.plateauBook
      TangentRound3Native.β2 TangentRound3Native.β3
      TangentRound3Native.plateauT)
    (1 / 1000000) (67 / 250) (3 / 8)
    TangentRound3Native.plateauMedium
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound3Native.plateau_checks.2.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_plateauBook] at hh
  norm_num [TangentRound3Native.β2, TangentRound3Native.β3,
    TangentRound3Native.plateauT, TangentAffine.c, Expr.eval] at hh
  positivity

private lemma r3_back1Coord :
    ∀ z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5),
      tangentXLog (3 / 100) z ≤
        tangentBLog (33 / 1000) (r3Back1TReal z) := by
  have h := affineLowerEval
    (TangentAffine.backwardLogCoord
      TangentRound3Native.β2 TangentRound3Native.β3
      TangentAffine.r3Back1T)
    0 (3 / 8) (3 / 5) TangentRound3Native.back1Fine
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound3Native.back1_checks.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_backwardLogCoord, eval_r3Back1T] at hh
  norm_num [TangentRound3Native.β2, TangentRound3Native.β3] at hh
  linarith

private lemma r3_back1Book :
    ∀ z ∈ Set.Icc (3 / 8 : ℝ) (3 / 5),
      0 < tangentCleanBookMargin (3 / 100) z
        (tangentALog (33 / 1000) (r3Back1TReal z) - Real.log z) := by
  have h := affineLowerEval
    (TangentAffine.backwardBook
      TangentRound3Native.β2 TangentRound3Native.β3
      TangentAffine.r3Back1T)
    (1 / 1000000) (3 / 8) (3 / 5)
    TangentRound3Native.back1Medium
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound3Native.back1_checks.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_backwardBook, eval_r3Back1T] at hh
  norm_num [TangentRound3Native.β2, TangentRound3Native.β3] at hh
  positivity

private lemma r3_back2Coord :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      tangentXLog (3 / 100) z ≤
        tangentBLog (33 / 1000) (r3Back2TReal z) := by
  have h := affineLowerEval
    (TangentAffine.backwardLogCoord
      TangentRound3Native.β2 TangentRound3Native.β3
      TangentAffine.r3Back2T)
    0 (3 / 5) 1 TangentRound3Native.back2Fine
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound3Native.back2_checks.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_backwardLogCoord, eval_r3Back2T] at hh
  norm_num [TangentRound3Native.β2, TangentRound3Native.β3] at hh
  linarith

private lemma r3_back2Book :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      0 < tangentCleanBookMargin (3 / 100) z
        (tangentALog (33 / 1000) (r3Back2TReal z) - Real.log z) := by
  have h := affineLowerEval
    (TangentAffine.backwardBook
      TangentRound3Native.β2 TangentRound3Native.β3
      TangentAffine.r3Back2T)
    (1 / 1000000) (3 / 5) 1
    TangentRound3Native.back2BookRefined
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound3Native.back2_checks.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_backwardBook, eval_r3Back2T] at hh
  norm_num [TangentRound3Native.β2, TangentRound3Native.β3] at hh
  positivity

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
