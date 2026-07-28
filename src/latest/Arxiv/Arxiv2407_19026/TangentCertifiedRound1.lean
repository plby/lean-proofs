import Arxiv.Arxiv2407_19026.TangentChecks1Front
import Arxiv.Arxiv2407_19026.TangentVerified

noncomputable section

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026

private lemma r1_smallCoordPrime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 10),
      (1 / 20 : ℝ) ≤
        tangentSmallCoordLogPrime (2 / 25) (9 / 200) z := by
  have h := affineLowerEval
    (TangentAffine.smallCoordSlope
      TangentRound1Native.β0 TangentRound1Native.β1)
    (1 / 20) 0 (1 / 10) TangentAffine.bpsSlope
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound1Native.small_checks.1
  intro z hz
  have hd := tangentSmall_domain
    (β := (TangentRound1Native.β1 : ℝ))
    (by norm_num [TangentRound1Native.β1]) hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_smallCoordSlope _ _ _
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2] at hh
  norm_num [TangentRound1Native.β0, TangentRound1Native.β1] at hh
  exact hh

private lemma r1_smallBookPrime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 50),
      (1 / 1000 : ℝ) ≤
        tangentSmallBookMarginPrime (2 / 25) (9 / 200) z := by
  have h := affineLowerEval
    (TangentAffine.smallBookSlope
      TangentRound1Native.β0 TangentRound1Native.β1)
    (1 / 1000) 0 (1 / 50) TangentAffine.bpsBookSlope
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound1Native.small_checks.2.1
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) (1 / 10) := by
    constructor
    · exact hz.1
    · nlinarith [hz.2]
  have hd := tangentSmall_domain
    (β := (TangentRound1Native.β1 : ℝ))
    (by norm_num [TangentRound1Native.β1]) hz'
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_smallBookSlope _ _ _
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2] at hh
  norm_num [TangentRound1Native.β0, TangentRound1Native.β1] at hh
  exact hh

private lemma r1_smallBook_lower :
    ∀ z ∈ Set.Icc (1 / 50 : ℝ) (1 / 10),
      (1 / 10000 : ℝ) ≤
        tangentSmallBookMargin (2 / 25) (9 / 200) z := by
  have h := affineLowerEval
    (TangentAffine.smallBook
      TangentRound1Native.β0 TangentRound1Native.β1)
    (1 / 10000) (1 / 50) (1 / 10) TangentAffine.bpsBook
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound1Native.small_checks.2.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_smallBook] at hh
  norm_num [TangentRound1Native.β0, TangentRound1Native.β1] at hh
  exact hh

private lemma r1_forwardCoord :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (269 / 1000),
      tangentXLog (9 / 200) z ≤
        tangentALog (2 / 25) (r1ForwardTReal z) := by
  have h := affineLowerEval
    (TangentAffine.forwardLogCoord
      TangentRound1Native.β0 TangentRound1Native.β1
      TangentAffine.r1ForwardT)
    0 (1 / 10) (269 / 1000)
    TangentRound1Native.forwardCoordRefined
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound1Native.forward_checks.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_forwardLogCoord, eval_r1ForwardT] at hh
  norm_num [TangentRound1Native.β0, TangentRound1Native.β1] at hh
  linarith

private lemma r1_forwardBook :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (269 / 1000),
      0 < tangentCleanBookMargin (9 / 200) z
        (tangentBLog (2 / 25) (r1ForwardTReal z) - Real.log z) := by
  have h := affineLowerEval
    (TangentAffine.forwardBook
      TangentRound1Native.β0 TangentRound1Native.β1
      TangentAffine.r1ForwardT)
    (1 / 1000000) (1 / 10) (269 / 1000)
    TangentRound1Native.forwardMedium
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound1Native.forward_checks.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_forwardBook, eval_r1ForwardT] at hh
  norm_num [TangentRound1Native.β0, TangentRound1Native.β1] at hh
  positivity

private lemma r1_plateauLow :
    ∀ z ∈ Set.Icc (269 / 1000 : ℝ) (387 / 1000),
      tangentBLog (2 / 25) (99 / 100) ≤ tangentXLog (9 / 200) z := by
  have h := affineLowerEval
    (TangentAffine.plateauLogLow
      TangentRound1Native.β0 TangentRound1Native.β1
      TangentRound1Native.plateauT)
    0 (269 / 1000) (387 / 1000)
    TangentRound1Native.plateauMedium
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound1Native.plateau_checks.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_plateauLogLow] at hh
  norm_num [TangentRound1Native.β0, TangentRound1Native.β1,
    TangentRound1Native.plateauT, TangentAffine.c, Expr.eval] at hh
  linarith

private lemma r1_plateauHigh :
    ∀ z ∈ Set.Icc (269 / 1000 : ℝ) (387 / 1000),
      tangentXLog (9 / 200) z ≤ tangentALog (2 / 25) (99 / 100) := by
  have h := affineLowerEval
    (TangentAffine.plateauLogHigh
      TangentRound1Native.β0 TangentRound1Native.β1
      TangentRound1Native.plateauT)
    0 (269 / 1000) (387 / 1000)
    TangentRound1Native.plateauMedium
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound1Native.plateau_checks.2.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_plateauLogHigh] at hh
  norm_num [TangentRound1Native.β0, TangentRound1Native.β1,
    TangentRound1Native.plateauT, TangentAffine.c, Expr.eval] at hh
  linarith

private lemma r1_plateauBook :
    ∀ z ∈ Set.Icc (269 / 1000 : ℝ) (387 / 1000),
      0 < tangentCleanBookMargin (9 / 200) z
        (tangentALog (2 / 25) (99 / 100) +
          tangentBLog (2 / 25) (99 / 100) -
          tangentXLog (9 / 200) z - Real.log z) := by
  have h := affineLowerEval
    (TangentAffine.plateauBook
      TangentRound1Native.β0 TangentRound1Native.β1
      TangentRound1Native.plateauT)
    (1 / 1000000) (269 / 1000) (387 / 1000)
    TangentRound1Native.plateauBookRefined
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound1Native.plateau_checks.2.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_plateauBook] at hh
  norm_num [TangentRound1Native.β0, TangentRound1Native.β1,
    TangentRound1Native.plateauT, TangentAffine.c, Expr.eval] at hh
  positivity

private lemma r1_back1Coord :
    ∀ z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5),
      tangentXLog (9 / 200) z ≤
        tangentBLog (2 / 25) (r1Back1TReal z) := by
  have h := affineLowerEval
    (TangentAffine.backwardLogCoord
      TangentRound1Native.β0 TangentRound1Native.β1
      TangentAffine.r1Back1T)
    0 (387 / 1000) (3 / 5) TangentRound1Native.back1Fine
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound1Native.back1_checks.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_backwardLogCoord, eval_r1Back1T] at hh
  norm_num [TangentRound1Native.β0, TangentRound1Native.β1] at hh
  linarith

private lemma r1_back1Book :
    ∀ z ∈ Set.Icc (387 / 1000 : ℝ) (3 / 5),
      0 < tangentCleanBookMargin (9 / 200) z
        (tangentALog (2 / 25) (r1Back1TReal z) - Real.log z) := by
  have h := affineLowerEval
    (TangentAffine.backwardBook
      TangentRound1Native.β0 TangentRound1Native.β1
      TangentAffine.r1Back1T)
    (1 / 1000000) (387 / 1000) (3 / 5)
    TangentRound1Native.back1Medium
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound1Native.back1_checks.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_backwardBook, eval_r1Back1T] at hh
  norm_num [TangentRound1Native.β0, TangentRound1Native.β1] at hh
  positivity

private lemma r1_back2Coord :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      tangentXLog (9 / 200) z ≤
        tangentBLog (2 / 25) (r1Back2TReal z) := by
  have h := affineLowerEval
    (TangentAffine.backwardLogCoord
      TangentRound1Native.β0 TangentRound1Native.β1
      TangentAffine.r1Back2T)
    0 (3 / 5) 1 TangentRound1Native.back2Fine
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound1Native.back2_checks.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_backwardLogCoord, eval_r1Back2T] at hh
  norm_num [TangentRound1Native.β0, TangentRound1Native.β1] at hh
  linarith

private lemma r1_back2Book :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      0 < tangentCleanBookMargin (9 / 200) z
        (tangentALog (2 / 25) (r1Back2TReal z) - Real.log z) := by
  have h := affineLowerEval
    (TangentAffine.backwardBook
      TangentRound1Native.β0 TangentRound1Native.β1
      TangentAffine.r1Back2T)
    (1 / 1000000) (3 / 5) 1 TangentRound1Native.back2Medium
    (Expr.checkSupportedCore_correct (by native_decide))
    (by native_decide) (by native_decide)
    TangentRound1Native.back2_checks.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_backwardBook, eval_r1Back2T] at hh
  norm_num [TangentRound1Native.β0, TangentRound1Native.β1] at hh
  positivity

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
