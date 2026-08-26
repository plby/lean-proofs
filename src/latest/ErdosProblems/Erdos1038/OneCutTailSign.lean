import ErdosProblems.Erdos1038.OneCutTailCertificate

namespace Erdos1038

noncomputable section

open Set
open IntervalExpr

namespace OneCutTailCertificate

theorem tailQ_lt_one : (tailQ : ℝ) < 1 := by
  norm_num [tailQ]

theorem tailQ_lt_qSoft : (tailQ : ℝ) < qSoft := by
  have hrat : (tailQ : ℝ) < (qSoftLowerRat : ℝ) := by
    norm_num [tailQ, qSoftLowerRat]
  exact hrat.trans qSoftLower_lt_qSoft

theorem tailVars_contains {q zp zm : ℝ}
    (hq : 0 < q) (hqTail : q ≤ (tailQ : ℝ))
    (hzp : zp ∈ Icc ((499 / 1000 : Rat) : ℝ)
      ((501 / 1000 : Rat) : ℝ))
    (hzm : zm ∈ Icc ((149 / 100 : Rat) : ℝ)
      ((15001 / 10000 : Rat) : ℝ)) :
    ∀ i, (tailVars i).Contains
      (![tailRReal q, q, tailQrReal q, zp, zm] i) := by
  intro i
  fin_cases i
  all_goals dsimp [tailVars, RatInterval.Contains]
  · exact ⟨by simpa only [Rat.cast_zero] using!
        (tailRReal_pos hq hqTail).le,
      tailRReal_le_fiftieth hq hqTail⟩
  · exact ⟨by simpa only [Rat.cast_zero] using! hq.le, hqTail⟩
  · exact ⟨by simpa only [Rat.cast_zero] using!
        (tailQrReal_pos hq hqTail).le,
      tailQrReal_le_tailQr hq hqTail⟩
  · exact hzp
  · exact hzm

private theorem innerLowerVars_contains {q : ℝ}
    (hq : 0 < q) (hqTail : q ≤ (tailQ : ℝ)) :
    ∀ i, (innerLowerVars i).Contains
      (![tailRReal q, q, tailQrReal q, ((499 / 1000 : Rat) : ℝ),
        ((149 / 100 : Rat) : ℝ)] i) := by
  intro i
  fin_cases i
  all_goals dsimp [innerLowerVars, tailVars, RatInterval.Contains,
    RatInterval.point]
  · exact ⟨by simpa only [Rat.cast_zero] using!
        (tailRReal_pos hq hqTail).le,
      tailRReal_le_fiftieth hq hqTail⟩
  · exact ⟨by simpa only [Rat.cast_zero] using! hq.le, hqTail⟩
  · exact ⟨by simpa only [Rat.cast_zero] using!
        (tailQrReal_pos hq hqTail).le,
      tailQrReal_le_tailQr hq hqTail⟩
  · exact ⟨le_rfl, le_rfl⟩
  · norm_num

private theorem innerUpperVars_contains {q : ℝ}
    (hq : 0 < q) (hqTail : q ≤ (tailQ : ℝ)) :
    ∀ i, (innerUpperVars i).Contains
      (![tailRReal q, q, tailQrReal q, ((501 / 1000 : Rat) : ℝ),
        ((149 / 100 : Rat) : ℝ)] i) := by
  intro i
  fin_cases i
  all_goals dsimp [innerUpperVars, tailVars, RatInterval.Contains,
    RatInterval.point]
  · exact ⟨by simpa only [Rat.cast_zero] using!
        (tailRReal_pos hq hqTail).le,
      tailRReal_le_fiftieth hq hqTail⟩
  · exact ⟨by simpa only [Rat.cast_zero] using! hq.le, hqTail⟩
  · exact ⟨by simpa only [Rat.cast_zero] using!
        (tailQrReal_pos hq hqTail).le,
      tailQrReal_le_tailQr hq hqTail⟩
  · exact ⟨le_rfl, le_rfl⟩
  · norm_num

private theorem outerLowerVars_contains {q : ℝ}
    (hq : 0 < q) (hqTail : q ≤ (tailQ : ℝ)) :
    ∀ i, (outerLowerVars i).Contains
      (![tailRReal q, q, tailQrReal q, ((499 / 1000 : Rat) : ℝ),
        ((149 / 100 : Rat) : ℝ)] i) := by
  intro i
  fin_cases i
  all_goals dsimp [outerLowerVars, tailVars, RatInterval.Contains,
    RatInterval.point]
  · exact ⟨by simpa only [Rat.cast_zero] using!
        (tailRReal_pos hq hqTail).le,
      tailRReal_le_fiftieth hq hqTail⟩
  · exact ⟨by simpa only [Rat.cast_zero] using! hq.le, hqTail⟩
  · exact ⟨by simpa only [Rat.cast_zero] using!
        (tailQrReal_pos hq hqTail).le,
      tailQrReal_le_tailQr hq hqTail⟩
  · norm_num
  · exact ⟨le_rfl, le_rfl⟩

private theorem outerUpperVars_contains {q : ℝ}
    (hq : 0 < q) (hqTail : q ≤ (tailQ : ℝ)) :
    ∀ i, (outerUpperVars i).Contains
      (![tailRReal q, q, tailQrReal q, ((499 / 1000 : Rat) : ℝ),
        ((15001 / 10000 : Rat) : ℝ)] i) := by
  intro i
  fin_cases i
  all_goals dsimp [outerUpperVars, tailVars, RatInterval.Contains,
    RatInterval.point]
  · exact ⟨by simpa only [Rat.cast_zero] using!
        (tailRReal_pos hq hqTail).le,
      tailRReal_le_fiftieth hq hqTail⟩
  · exact ⟨by simpa only [Rat.cast_zero] using! hq.le, hqTail⟩
  · exact ⟨by simpa only [Rat.cast_zero] using!
        (tailQrReal_pos hq hqTail).le,
      tailQrReal_le_tailQr hq hqTail⟩
  · norm_num
  · exact ⟨le_rfl, le_rfl⟩

theorem scaledRoots_mem_tail_box {q : ℝ}
    (hq : 0 < q) (hqTail : q ≤ (tailQ : ℝ)) :
    zPlus q ∈ Ioo ((499 / 1000 : Rat) : ℝ)
        ((501 / 1000 : Rat) : ℝ) ∧
      zMinus q ∈ Ioo ((149 / 100 : Rat) : ℝ)
        ((15001 / 10000 : Rat) : ℝ) := by
  have hq1 : q < 1 := hqTail.trans_lt tailQ_lt_one
  have hqs : q < qSoft := hqTail.trans_lt tailQ_lt_qSoft
  have hpLoTail := evalNegative_sound innerLowerVars_ordered
    (innerLowerVars_contains hq hqTail) innerLower_certified
  have hpHiTail := evalPositive_sound innerUpperVars_ordered
    (innerUpperVars_contains hq hqTail) innerUpper_certified
  have hmLoTail := evalPositive_sound outerLowerVars_ordered
    (outerLowerVars_contains hq hqTail) outerLower_certified
  have hmHiTail := evalNegative_sound outerUpperVars_ordered
    (outerUpperVars_contains hq hqTail) outerUpper_certified
  rw [tailInnerGExpr_eval,
    tailInnerGReal_eq_scaledInnerResidual hq hq1] at hpLoTail hpHiTail
  rw [tailOuterGExpr_eval,
    tailOuterGReal_eq_scaledOuterResidual hq hq1] at hmLoTail hmHiTail
  apply scaledRoots_mem_Ioo_of_endpoint_signs hq hqs
  · exact hqTail.trans_lt (by norm_num [tailQ])
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpLoTail
  · exact hpHiTail
  · exact hmLoTail
  · exact hmHiTail

theorem lambdaDerivativeFormula_neg_of_le_tailQ {q : ℝ}
    (hq : 0 < q) (hqTail : q ≤ (tailQ : ℝ)) :
    LambdaDerivativeFormula q < 0 := by
  have hq1 : q < 1 := hqTail.trans_lt tailQ_lt_one
  have hqs : q < qSoft := hqTail.trans_lt tailQ_lt_qSoft
  have hroots := scaledRoots_mem_tail_box hq hqTail
  have hcontains := tailVars_contains hq hqTail
    ⟨hroots.1.1.le, hroots.1.2.le⟩
    ⟨hroots.2.1.le, hroots.2.2.le⟩
  have htail := evalNegative_sound tailVars_ordered hcontains
    lambdaR_certified
  rw [tailLambdaRExpr_eval,
    tailLambdaRReal_eq_scaled_mul hq hq1] at htail
  have hspeed := tailQrReal_pos hq hqTail
  have hscaled :
      scaledLambdaDerivativeAt q (zPlus q) (zMinus q) < 0 := by
    by_contra hn
    have hnonneg :
        0 ≤ scaledLambdaDerivativeAt q (zPlus q) (zMinus q) :=
      le_of_not_gt hn
    have := mul_nonneg hnonneg hspeed.le
    linarith
  rw [LambdaDerivativeFormula_eq_scaled hq hqs,
    scaledLambdaDerivativeFormula_eq_at]
  exact hscaled

end OneCutTailCertificate

end

end Erdos1038
