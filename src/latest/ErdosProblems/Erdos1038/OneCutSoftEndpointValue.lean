import ErdosProblems.Erdos1038.OneCutNewtonBox
import ErdosProblems.Erdos1038.KernelDecision

set_option maxRecDepth 100000

/-!
# The one-cut soft endpoint lies above the stationary value
-/

open Set

namespace Erdos1038

noncomputable section

open IntervalExpr

namespace OneCutSoftEndpointValue

def qBox : RatInterval := ⟨qSoftLowerRat, qSoftUpperRat⟩

def zmBox : RatInterval := ⟨149 / 100, 150 / 100⟩

def outerLowerVars : Fin 3 → RatInterval :=
  ![qBox, RatInterval.point 1, RatInterval.point zmBox.lo]

def outerUpperVars : Fin 3 → RatInterval :=
  ![qBox, RatInterval.point 1, RatInterval.point zmBox.hi]

def valueVars : Fin 3 → RatInterval := ![qBox, qBox, zmBox]

theorem outer_lower_positive :
    EvalPositive outerLowerVars (outerResidualExpr 80 6) := by
  kernel_decide

theorem outer_upper_negative :
    EvalNegative outerUpperVars (outerResidualExpr 80 6) := by
  kernel_decide

theorem value_above_minimum_upper :
    EvalPositive valueVars (.sub lambdaExpr (.rat lambdaUpperRat)) := by
  kernel_decide

private theorem qBox_ordered : qBox.Ordered := by
  norm_num [qBox, RatInterval.Ordered, qSoftLowerRat, qSoftUpperRat]

private theorem zmBox_ordered : zmBox.Ordered := by
  norm_num [zmBox, RatInterval.Ordered]

private theorem qSoft_mem_qBox : qBox.Contains qSoft :=
  ⟨qSoftLower_lt_qSoft.le, qSoft_lt_qSoftUpper.le⟩

private theorem outerLowerVars_ordered :
    ∀ i, (outerLowerVars i).Ordered := by
  intro i
  fin_cases i
  · exact qBox_ordered
  · exact RatInterval.point_ordered _
  · exact RatInterval.point_ordered _

private theorem outerUpperVars_ordered :
    ∀ i, (outerUpperVars i).Ordered := by
  intro i
  fin_cases i
  · exact qBox_ordered
  · exact RatInterval.point_ordered _
  · exact RatInterval.point_ordered _

private theorem valueVars_ordered : ∀ i, (valueVars i).Ordered := by
  intro i
  fin_cases i
  · exact qBox_ordered
  · exact qBox_ordered
  · exact zmBox_ordered

theorem zMinus_qSoft_mem : zMinus qSoft ∈ Ioo (zmBox.lo : ℝ) (zmBox.hi : ℝ) := by
  have hq : 0 < qSoft := qSoft_mem_Ioo.1
  have hlo : 0 < scaledOuterResidual (qSoft, (zmBox.lo : ℝ)) := by
    have hcontains : ∀ i, (outerLowerVars i).Contains
        (![qSoft, 1, (zmBox.lo : ℝ)] i) := by
      intro i
      fin_cases i
      · exact qSoft_mem_qBox
      · simpa [outerLowerVars] using! RatInterval.point_contains (1 : Rat)
      · simpa [outerLowerVars] using! RatInterval.point_contains zmBox.lo
    have hs := evalPositive_sound outerLowerVars_ordered hcontains
      outer_lower_positive
    rwa [outerResidualExpr_eval] at hs
  have hhi : scaledOuterResidual (qSoft, (zmBox.hi : ℝ)) < 0 := by
    have hcontains : ∀ i, (outerUpperVars i).Contains
        (![qSoft, 1, (zmBox.hi : ℝ)] i) := by
      intro i
      fin_cases i
      · exact qSoft_mem_qBox
      · simpa [outerUpperVars] using! RatInterval.point_contains (1 : Rat)
      · simpa [outerUpperVars] using! RatInterval.point_contains zmBox.hi
    have hs := evalNegative_sound outerUpperVars_ordered hcontains
      outer_upper_negative
    rwa [outerResidualExpr_eval] at hs
  constructor
  · apply scaledOuterResidual_pos_imp_lt_zMinus hq le_rfl
      (by norm_num [zmBox]) hlo
  · apply scaledOuterResidual_neg_imp_zMinus_lt hq le_rfl
      (by norm_num [zmBox]) hhi

theorem Lambda_qSoft_eq_scaled :
    Lambda qSoft = scaledLambdaExpression qSoft qSoft (zMinus qSoft) := by
  have hq : 0 < qSoft := qSoft_mem_Ioo.1
  have hu : 0 < uMinus qSoft :=
    (inv_pos.mpr hq).trans (uMinus_spec hq le_rfl).1
  have hden : 1 + qSoft ≠ 0 := by linarith
  have hup : uPlus qSoft = 1 := by simp [uPlus]
  rw [Lambda, scaledLambdaExpression, zMinus, H, hup]
  field_simp [hq.ne', hu.ne', hden]
  ring

theorem lambdaUpper_lt_Lambda_qSoft :
    (lambdaUpperRat : ℝ) < Lambda qSoft := by
  have hcontains : ∀ i, (valueVars i).Contains
      (![qSoft, qSoft, zMinus qSoft] i) := by
    intro i
    fin_cases i
    · exact qSoft_mem_qBox
    · exact qSoft_mem_qBox
    · exact ⟨zMinus_qSoft_mem.1.le, zMinus_qSoft_mem.2.le⟩
  have hs := evalPositive_sound valueVars_ordered hcontains
    value_above_minimum_upper
  have heval : evalReal ![qSoft, qSoft, zMinus qSoft]
      (.sub lambdaExpr (.rat lambdaUpperRat)) =
      scaledLambdaExpression qSoft qSoft (zMinus qSoft) -
        (lambdaUpperRat : ℝ) := by
    simp [IntervalExpr.sub, evalReal, lambdaExpr_eval, sub_eq_add_neg]
  rw [heval] at hs
  rw [Lambda_qSoft_eq_scaled]
  linarith

end OneCutSoftEndpointValue

end

end Erdos1038
