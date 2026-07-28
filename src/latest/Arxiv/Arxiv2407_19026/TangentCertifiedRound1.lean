import Arxiv.Arxiv2407_19026.TangentChecks1Front
import Arxiv.Arxiv2407_19026.TangentVerified

noncomputable section

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026

private lemma bpsSlope_ne : TangentAffine.bpsSlope ≠ [] := by
  unfold TangentAffine.bpsSlope
  exact TangentAffine.mappedCoeRange_ne _ 10 (by norm_num)

private lemma bpsSlope_last :
    TangentAffine.bpsSlope.getLast bpsSlope_ne = 1 / 10 := by
  unfold TangentAffine.bpsSlope
  convert TangentAffine.mappedCoeRange_getLast
    _ 10 (by norm_num) bpsSlope_ne using 1
  all_goals norm_num

private lemma bpsBookSlope_ne : TangentAffine.bpsBookSlope ≠ [] := by
  unfold TangentAffine.bpsBookSlope
  exact TangentAffine.mappedCoeRange_ne _ 20 (by norm_num)

private lemma bpsBookSlope_last :
    TangentAffine.bpsBookSlope.getLast bpsBookSlope_ne = 1 / 50 := by
  unfold TangentAffine.bpsBookSlope
  convert TangentAffine.mappedCoeRange_getLast
    _ 20 (by norm_num) bpsBookSlope_ne using 1
  all_goals norm_num

private lemma bpsBook_ne : TangentAffine.bpsBook ≠ [] := by
  unfold TangentAffine.bpsBook
  exact TangentAffine.mappedCoeRange_ne _ 80 (by norm_num)

private lemma bpsBook_last :
    TangentAffine.bpsBook.getLast bpsBook_ne = 1 / 10 := by
  unfold TangentAffine.bpsBook
  convert TangentAffine.mappedCoeRange_getLast
    _ 80 (by norm_num) bpsBook_ne using 1
  all_goals norm_num

private lemma r1ForwardCoordRefined_ne :
    TangentRound1Native.forwardCoordRefined ≠ [] := by
  unfold TangentRound1Native.forwardCoordRefined
  apply TangentAffine.flatMapRange_ne _ 1690 (by norm_num)
  simp

private lemma r1ForwardCoordRefined_last :
    TangentRound1Native.forwardCoordRefined.getLast
      r1ForwardCoordRefined_ne = 269 / 1000 := by
  unfold TangentRound1Native.forwardCoordRefined
  have hlast :
      (fun n => [((2 * n + 2001 : Nat) : ℚ) / 20000,
        ((n + 1001 : Nat) : ℚ) / 10000]) (1690 - 1) ≠ [] := by
    simp
  rw [TangentAffine.flatMapRange_getLast
    _ 1690 (by norm_num) hlast r1ForwardCoordRefined_ne]
  norm_num

private lemma r1ForwardMedium_ne :
    TangentRound1Native.forwardMedium ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 100 169 (by norm_num)

private lemma r1ForwardMedium_last :
    TangentRound1Native.forwardMedium.getLast r1ForwardMedium_ne =
      269 / 1000 := by
  unfold TangentRound1Native.forwardMedium
  convert TangentAffine.mediumBreakpoints_getLast
    100 169 (by norm_num) r1ForwardMedium_ne using 1
  all_goals norm_num

private lemma r1PlateauMedium_ne :
    TangentRound1Native.plateauMedium ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 269 118 (by norm_num)

private lemma r1PlateauMedium_last :
    TangentRound1Native.plateauMedium.getLast r1PlateauMedium_ne =
      387 / 1000 := by
  unfold TangentRound1Native.plateauMedium
  convert TangentAffine.mediumBreakpoints_getLast
    269 118 (by norm_num) r1PlateauMedium_ne using 1
  all_goals norm_num

private lemma r1PlateauBookRefined_ne :
    TangentRound1Native.plateauBookRefined ≠ [] := by
  unfold TangentRound1Native.plateauBookRefined
  apply List.append_ne_nil_of_right_ne_nil
  exact TangentAffine.mediumBreakpoints_ne 379 8 (by norm_num)

private lemma r1PlateauBookRefined_last :
    TangentRound1Native.plateauBookRefined.getLast
      r1PlateauBookRefined_ne = 387 / 1000 := by
  unfold TangentRound1Native.plateauBookRefined
  have hr := TangentAffine.mediumBreakpoints_ne 379 8 (by norm_num)
  rw [List.getLast_append_of_right_ne_nil _ _ hr]
  convert TangentAffine.mediumBreakpoints_getLast
    379 8 (by norm_num) hr using 1
  all_goals norm_num

private lemma r1Back1Fine_ne : TangentRound1Native.back1Fine ≠ [] := by
  exact TangentAffine.fineBreakpoints_ne 3870 2130 (by norm_num)

private lemma r1Back1Fine_last :
    TangentRound1Native.back1Fine.getLast r1Back1Fine_ne = 3 / 5 := by
  unfold TangentRound1Native.back1Fine
  convert TangentAffine.fineBreakpoints_getLast
    3870 2130 (by norm_num) r1Back1Fine_ne using 1
  all_goals norm_num

private lemma r1Back1Medium_ne :
    TangentRound1Native.back1Medium ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 387 213 (by norm_num)

private lemma r1Back1Medium_last :
    TangentRound1Native.back1Medium.getLast r1Back1Medium_ne = 3 / 5 := by
  unfold TangentRound1Native.back1Medium
  convert TangentAffine.mediumBreakpoints_getLast
    387 213 (by norm_num) r1Back1Medium_ne using 1
  all_goals norm_num

private lemma r1Back2Fine_ne : TangentRound1Native.back2Fine ≠ [] := by
  exact TangentAffine.fineBreakpoints_ne 6000 4000 (by norm_num)

private lemma r1Back2Fine_last :
    TangentRound1Native.back2Fine.getLast r1Back2Fine_ne = 1 := by
  unfold TangentRound1Native.back2Fine
  convert TangentAffine.fineBreakpoints_getLast
    6000 4000 (by norm_num) r1Back2Fine_ne using 1
  all_goals norm_num

private lemma r1Back2Medium_ne :
    TangentRound1Native.back2Medium ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 600 400 (by norm_num)

private lemma r1Back2Medium_last :
    TangentRound1Native.back2Medium.getLast r1Back2Medium_ne = 1 := by
  unfold TangentRound1Native.back2Medium
  convert TangentAffine.mediumBreakpoints_getLast
    600 400 (by norm_num) r1Back2Medium_ne using 1
  all_goals norm_num

private lemma r1_smallCoordPrime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 10),
      (1 / 20 : ℝ) ≤
        tangentSmallCoordLogPrime (2 / 25) (9 / 200) z := by
  have h := affineLowerEval
    (TangentAffine.smallCoordSlope
      TangentRound1Native.β0 TangentRound1Native.β1)
    (1 / 20) 0 (1 / 10) TangentAffine.bpsSlope
    (Expr.checkSupportedCore_correct (by decide))
    bpsSlope_ne bpsSlope_last
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
    (Expr.checkSupportedCore_correct (by decide))
    bpsBookSlope_ne bpsBookSlope_last
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
    (Expr.checkSupportedCore_correct (by decide))
    bpsBook_ne bpsBook_last
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
    (Expr.checkSupportedCore_correct (by decide))
    r1ForwardCoordRefined_ne r1ForwardCoordRefined_last
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
    (Expr.checkSupportedCore_correct (by decide))
    r1ForwardMedium_ne r1ForwardMedium_last
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
    (Expr.checkSupportedCore_correct (by decide))
    r1PlateauMedium_ne r1PlateauMedium_last
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
    (Expr.checkSupportedCore_correct (by decide))
    r1PlateauMedium_ne r1PlateauMedium_last
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
    (Expr.checkSupportedCore_correct (by decide))
    r1PlateauBookRefined_ne r1PlateauBookRefined_last
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
    (Expr.checkSupportedCore_correct (by decide))
    r1Back1Fine_ne r1Back1Fine_last
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
    (Expr.checkSupportedCore_correct (by decide))
    r1Back1Medium_ne r1Back1Medium_last
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
    (Expr.checkSupportedCore_correct (by decide))
    r1Back2Fine_ne r1Back2Fine_last
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
    (Expr.checkSupportedCore_correct (by decide))
    r1Back2Medium_ne r1Back2Medium_last
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
