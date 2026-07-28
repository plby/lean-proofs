import Arxiv.Arxiv2407_19026.TangentChecks2Front
import Arxiv.Arxiv2407_19026.TangentCertifiedRound1

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

private lemma r2ForwardCoordRefined_ne :
    TangentRound2Native.forwardCoordRefined ≠ [] := by
  unfold TangentRound2Native.forwardCoordRefined
  apply TangentAffine.flatMapRange_ne _ 1680 (by norm_num)
  simp

private lemma r2ForwardCoordRefined_last :
    TangentRound2Native.forwardCoordRefined.getLast
      r2ForwardCoordRefined_ne = 67 / 250 := by
  unfold TangentRound2Native.forwardCoordRefined
  have hlast :
      (fun n => [((2 * n + 2001 : Nat) : ℚ) / 20000,
        ((n + 1001 : Nat) : ℚ) / 10000]) (1680 - 1) ≠ [] := by
    simp
  rw [TangentAffine.flatMapRange_getLast
    _ 1680 (by norm_num) hlast r2ForwardCoordRefined_ne]
  norm_num

private lemma r2ForwardMedium_ne :
    TangentRound2Native.forwardMedium ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 100 168 (by norm_num)

private lemma r2ForwardMedium_last :
    TangentRound2Native.forwardMedium.getLast r2ForwardMedium_ne =
      67 / 250 := by
  unfold TangentRound2Native.forwardMedium
  convert TangentAffine.mediumBreakpoints_getLast
    100 168 (by norm_num) r2ForwardMedium_ne using 1
  all_goals norm_num

private lemma r2PlateauMedium_ne :
    TangentRound2Native.plateauMedium ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 268 110 (by norm_num)

private lemma r2PlateauMedium_last :
    TangentRound2Native.plateauMedium.getLast r2PlateauMedium_ne =
      189 / 500 := by
  unfold TangentRound2Native.plateauMedium
  convert TangentAffine.mediumBreakpoints_getLast
    268 110 (by norm_num) r2PlateauMedium_ne using 1
  all_goals norm_num

private lemma r2PlateauBookRefined_ne :
    TangentRound2Native.plateauBookRefined ≠ [] := by
  unfold TangentRound2Native.plateauBookRefined
  apply List.append_ne_nil_of_right_ne_nil
  exact TangentAffine.mediumBreakpoints_ne 367 11 (by norm_num)

private lemma r2PlateauBookRefined_last :
    TangentRound2Native.plateauBookRefined.getLast
      r2PlateauBookRefined_ne = 189 / 500 := by
  unfold TangentRound2Native.plateauBookRefined
  have hr := TangentAffine.mediumBreakpoints_ne 367 11 (by norm_num)
  rw [List.getLast_append_of_right_ne_nil _ _ hr]
  convert TangentAffine.mediumBreakpoints_getLast
    367 11 (by norm_num) hr using 1
  all_goals norm_num

private lemma r2Back1Fine_ne : TangentRound2Native.back1Fine ≠ [] := by
  exact TangentAffine.fineBreakpoints_ne 3780 2220 (by norm_num)

private lemma r2Back1Fine_last :
    TangentRound2Native.back1Fine.getLast r2Back1Fine_ne = 3 / 5 := by
  unfold TangentRound2Native.back1Fine
  convert TangentAffine.fineBreakpoints_getLast
    3780 2220 (by norm_num) r2Back1Fine_ne using 1
  all_goals norm_num

private lemma r2Back1Medium_ne :
    TangentRound2Native.back1Medium ≠ [] := by
  exact TangentAffine.mediumBreakpoints_ne 378 222 (by norm_num)

private lemma r2Back1Medium_last :
    TangentRound2Native.back1Medium.getLast r2Back1Medium_ne = 3 / 5 := by
  unfold TangentRound2Native.back1Medium
  convert TangentAffine.mediumBreakpoints_getLast
    378 222 (by norm_num) r2Back1Medium_ne using 1
  all_goals norm_num

private lemma r2Back2Fine_ne : TangentRound2Native.back2Fine ≠ [] := by
  exact TangentAffine.fineBreakpoints_ne 6000 4000 (by norm_num)

private lemma r2Back2Fine_last :
    TangentRound2Native.back2Fine.getLast r2Back2Fine_ne = 1 := by
  unfold TangentRound2Native.back2Fine
  convert TangentAffine.fineBreakpoints_getLast
    6000 4000 (by norm_num) r2Back2Fine_ne using 1
  all_goals norm_num

private lemma r2Back2BookRefined_ne :
    TangentRound2Native.back2BookRefined ≠ [] := by
  unfold TangentRound2Native.back2BookRefined
  apply List.append_ne_nil_of_right_ne_nil
  apply TangentAffine.flatMapRange_ne _ 16 (by norm_num)
  exact TangentAffine.mappedRange_ne _ 10 (by norm_num)

private lemma r2Back2BookRefined_last :
    TangentRound2Native.back2BookRefined.getLast
      r2Back2BookRefined_ne = 1 := by
  unfold TangentRound2Native.back2BookRefined
  have hblock :
      (fun n => (List.range 10).map
        (fun j => ((10 * (n + 984) + j + 1 : Nat) : ℚ) / 10000))
        (16 - 1) ≠ [] :=
    TangentAffine.mappedRange_ne _ 10 (by norm_num)
  have hr :
      (List.range 16).flatMap (fun n =>
        (List.range 10).map
          (fun j => ((10 * (n + 984) + j + 1 : Nat) : ℚ) / 10000)) ≠ [] :=
    TangentAffine.flatMapRange_ne _ 16 (by norm_num) hblock
  rw [List.getLast_append_of_right_ne_nil _ _ hr]
  rw [TangentAffine.flatMapRange_getLast
    _ 16 (by norm_num) hblock hr]
  rw [TangentAffine.mappedRange_getLast _ 10 hblock]
  norm_num

private lemma r2_smallCoordPrime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 10),
      (1 / 20 : ℝ) ≤
        tangentSmallCoordLogPrime (9 / 200) (33 / 1000) z := by
  have h := affineLowerEval
    (TangentAffine.smallCoordSlope
      TangentRound2Native.β1 TangentRound2Native.β2)
    (1 / 20) 0 (1 / 10) TangentAffine.bpsSlope
    (Expr.checkSupportedCore_correct (by decide))
    bpsSlope_ne bpsSlope_last
    TangentRound2Native.small_checks.1
  intro z hz
  have hd := tangentSmall_domain
    (β := (TangentRound2Native.β2 : ℝ))
    (by norm_num [TangentRound2Native.β2]) hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_smallCoordSlope _ _ _
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2] at hh
  norm_num [TangentRound2Native.β1, TangentRound2Native.β2] at hh
  exact hh

private lemma r2_smallBookPrime_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 50),
      (1 / 1000 : ℝ) ≤
        tangentSmallBookMarginPrime (9 / 200) (33 / 1000) z := by
  have h := affineLowerEval
    (TangentAffine.smallBookSlope
      TangentRound2Native.β1 TangentRound2Native.β2)
    (1 / 1000) 0 (1 / 50) TangentAffine.bpsBookSlope
    (Expr.checkSupportedCore_correct (by decide))
    bpsBookSlope_ne bpsBookSlope_last
    TangentRound2Native.small_checks.2.1
  intro z hz
  have hz' : z ∈ Set.Icc (0 : ℝ) (1 / 10) := by
    constructor
    · exact hz.1
    · nlinarith [hz.2]
  have hd := tangentSmall_domain
    (β := (TangentRound2Native.β2 : ℝ))
    (by norm_num [TangentRound2Native.β2]) hz'
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_smallBookSlope _ _ _
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2] at hh
  norm_num [TangentRound2Native.β1, TangentRound2Native.β2] at hh
  exact hh

private lemma r2_smallBook_lower :
    ∀ z ∈ Set.Icc (1 / 50 : ℝ) (1 / 10),
      (1 / 10000 : ℝ) ≤
        tangentSmallBookMargin (9 / 200) (33 / 1000) z := by
  have h := affineLowerEval
    (TangentAffine.smallBook
      TangentRound2Native.β1 TangentRound2Native.β2)
    (1 / 10000) (1 / 50) (1 / 10) TangentAffine.bpsBook
    (Expr.checkSupportedCore_correct (by decide))
    bpsBook_ne bpsBook_last
    TangentRound2Native.small_checks.2.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_smallBook] at hh
  norm_num [TangentRound2Native.β1, TangentRound2Native.β2] at hh
  exact hh

private lemma r2_forwardCoord :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      tangentXLog (33 / 1000) z ≤
        tangentALog (9 / 200) (r2ForwardTReal z) := by
  have h := affineLowerEval
    (TangentAffine.forwardLogCoord
      TangentRound2Native.β1 TangentRound2Native.β2
      TangentAffine.r2ForwardT)
    0 (1 / 10) (67 / 250)
    TangentRound2Native.forwardCoordRefined
    (Expr.checkSupportedCore_correct (by decide))
    r2ForwardCoordRefined_ne r2ForwardCoordRefined_last
    TangentRound2Native.forward_checks.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_forwardLogCoord, eval_r2ForwardT] at hh
  norm_num [TangentRound2Native.β1, TangentRound2Native.β2] at hh
  linarith

private lemma r2_forwardBook :
    ∀ z ∈ Set.Icc (1 / 10 : ℝ) (67 / 250),
      0 < tangentCleanBookMargin (33 / 1000) z
        (tangentBLog (9 / 200) (r2ForwardTReal z) - Real.log z) := by
  have h := affineLowerEval
    (TangentAffine.forwardBook
      TangentRound2Native.β1 TangentRound2Native.β2
      TangentAffine.r2ForwardT)
    (1 / 1000000) (1 / 10) (67 / 250)
    TangentRound2Native.forwardMedium
    (Expr.checkSupportedCore_correct (by decide))
    r2ForwardMedium_ne r2ForwardMedium_last
    TangentRound2Native.forward_checks.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_forwardBook, eval_r2ForwardT] at hh
  norm_num [TangentRound2Native.β1, TangentRound2Native.β2] at hh
  positivity

private lemma r2_plateauLow :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (189 / 500),
      tangentBLog (9 / 200) (99 / 100) ≤ tangentXLog (33 / 1000) z := by
  have h := affineLowerEval
    (TangentAffine.plateauLogLow
      TangentRound2Native.β1 TangentRound2Native.β2
      TangentRound2Native.plateauT)
    0 (67 / 250) (189 / 500)
    TangentRound2Native.plateauMedium
    (Expr.checkSupportedCore_correct (by decide))
    r2PlateauMedium_ne r2PlateauMedium_last
    TangentRound2Native.plateau_checks.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_plateauLogLow] at hh
  norm_num [TangentRound2Native.β1, TangentRound2Native.β2,
    TangentRound2Native.plateauT, TangentAffine.c, Expr.eval] at hh
  linarith

private lemma r2_plateauHigh :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (189 / 500),
      tangentXLog (33 / 1000) z ≤ tangentALog (9 / 200) (99 / 100) := by
  have h := affineLowerEval
    (TangentAffine.plateauLogHigh
      TangentRound2Native.β1 TangentRound2Native.β2
      TangentRound2Native.plateauT)
    0 (67 / 250) (189 / 500)
    TangentRound2Native.plateauMedium
    (Expr.checkSupportedCore_correct (by decide))
    r2PlateauMedium_ne r2PlateauMedium_last
    TangentRound2Native.plateau_checks.2.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_plateauLogHigh] at hh
  norm_num [TangentRound2Native.β1, TangentRound2Native.β2,
    TangentRound2Native.plateauT, TangentAffine.c, Expr.eval] at hh
  linarith

private lemma r2_plateauBook :
    ∀ z ∈ Set.Icc (67 / 250 : ℝ) (189 / 500),
      0 < tangentCleanBookMargin (33 / 1000) z
        (tangentALog (9 / 200) (99 / 100) +
          tangentBLog (9 / 200) (99 / 100) -
          tangentXLog (33 / 1000) z - Real.log z) := by
  have h := affineLowerEval
    (TangentAffine.plateauBook
      TangentRound2Native.β1 TangentRound2Native.β2
      TangentRound2Native.plateauT)
    (1 / 1000000) (67 / 250) (189 / 500)
    TangentRound2Native.plateauBookRefined
    (Expr.checkSupportedCore_correct (by decide))
    r2PlateauBookRefined_ne r2PlateauBookRefined_last
    TangentRound2Native.plateau_checks.2.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_plateauBook] at hh
  norm_num [TangentRound2Native.β1, TangentRound2Native.β2,
    TangentRound2Native.plateauT, TangentAffine.c, Expr.eval] at hh
  positivity

private lemma r2_back1Coord :
    ∀ z ∈ Set.Icc (189 / 500 : ℝ) (3 / 5),
      tangentXLog (33 / 1000) z ≤
        tangentBLog (9 / 200) (r2Back1TReal z) := by
  have h := affineLowerEval
    (TangentAffine.backwardLogCoord
      TangentRound2Native.β1 TangentRound2Native.β2
      TangentAffine.r2Back1T)
    0 (189 / 500) (3 / 5) TangentRound2Native.back1Fine
    (Expr.checkSupportedCore_correct (by decide))
    r2Back1Fine_ne r2Back1Fine_last
    TangentRound2Native.back1_checks.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_backwardLogCoord, eval_r2Back1T] at hh
  norm_num [TangentRound2Native.β1, TangentRound2Native.β2] at hh
  linarith

private lemma r2_back1Book :
    ∀ z ∈ Set.Icc (189 / 500 : ℝ) (3 / 5),
      0 < tangentCleanBookMargin (33 / 1000) z
        (tangentALog (9 / 200) (r2Back1TReal z) - Real.log z) := by
  have h := affineLowerEval
    (TangentAffine.backwardBook
      TangentRound2Native.β1 TangentRound2Native.β2
      TangentAffine.r2Back1T)
    (1 / 1000000) (189 / 500) (3 / 5)
    TangentRound2Native.back1Medium
    (Expr.checkSupportedCore_correct (by decide))
    r2Back1Medium_ne r2Back1Medium_last
    TangentRound2Native.back1_checks.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_backwardBook, eval_r2Back1T] at hh
  norm_num [TangentRound2Native.β1, TangentRound2Native.β2] at hh
  positivity

private lemma r2_back2Coord :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      tangentXLog (33 / 1000) z ≤
        tangentBLog (9 / 200) (r2Back2TReal z) := by
  have h := affineLowerEval
    (TangentAffine.backwardLogCoord
      TangentRound2Native.β1 TangentRound2Native.β2
      TangentAffine.r2Back2T)
    0 (3 / 5) 1 TangentRound2Native.back2Fine
    (Expr.checkSupportedCore_correct (by decide))
    r2Back2Fine_ne r2Back2Fine_last
    TangentRound2Native.back2_checks.1
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_backwardLogCoord, eval_r2Back2T] at hh
  norm_num [TangentRound2Native.β1, TangentRound2Native.β2] at hh
  linarith

private lemma r2_back2Book :
    ∀ z ∈ Set.Icc (3 / 5 : ℝ) 1,
      0 < tangentCleanBookMargin (33 / 1000) z
        (tangentALog (9 / 200) (r2Back2TReal z) - Real.log z) := by
  have h := affineLowerEval
    (TangentAffine.backwardBook
      TangentRound2Native.β1 TangentRound2Native.β2
      TangentAffine.r2Back2T)
    (1 / 1000000) (3 / 5) 1
    TangentRound2Native.back2BookRefined
    (Expr.checkSupportedCore_correct (by decide))
    r2Back2BookRefined_ne r2Back2BookRefined_last
    TangentRound2Native.back2_checks.2
  intro z hz
  have hh := h z (by norm_num at hz ⊢; exact hz)
  rw [TangentAffine.eval_backwardBook, eval_r2Back2T] at hh
  norm_num [TangentRound2Native.β1, TangentRound2Native.β2] at hh
  positivity

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
