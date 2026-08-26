import ErdosProblems.Erdos1038.OneCutLocalConvexCover20Certificate
import ErdosProblems.Erdos1038.OneCutRegularSignCover
import ErdosProblems.Erdos1038.OneCutStationaryPoint
import ErdosProblems.Erdos1038.OneCutTailSign
import ErdosProblems.Erdos1038.OneCutSoftSign

/-!
# Global exact derivative signs around the one-cut stationary point
-/

open Set

namespace Erdos1038

noncomputable section

open OneCutTailCertificate
open OneCutTailCertificate.OneCutRegularSignCover
open OneCutLocalConvexCover20
open OneCutStationaryPoint

private theorem c_mem_local :
    c ∈ Ioo (localStart : ℝ) (localFinish : ℝ) := by
  constructor
  · exact (by
      norm_num [localStart, OneCutStationaryBox.qLeftRat,
        OneCutStationaryBox.qCenterRat, OneCutStationaryBox.qRadiusRat] :
        (localStart : ℝ) < (OneCutStationaryBox.qLeftRat : ℝ)).trans c_mem.1
  · exact c_mem.2.trans (by
      norm_num [localFinish, OneCutStationaryBox.qRightRat,
        OneCutStationaryBox.qCenterRat, OneCutStationaryBox.qRadiusRat] :
        (OneCutStationaryBox.qRightRat : ℝ) < (localFinish : ℝ))

theorem lambdaDerivativeFormula_neg_global {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) c) :
    LambdaDerivativeFormula q < 0 := by
  by_cases htail : q ≤ (tailQ : ℝ)
  · exact lambdaDerivativeFormula_neg_of_le_tailQ hq.1 htail
  by_cases hlocal : q ≤ (localStart : ℝ)
  · exact lambdaDerivativeFormula_neg_regular
      ⟨(lt_of_not_ge htail).le, hlocal⟩
  · have hmono := strictMonoOn_lambdaDerivativeFormula_local
      ⟨(lt_of_not_ge hlocal).le, hq.2.le.trans c_mem_local.2.le⟩
      ⟨c_mem_local.1.le, c_mem_local.2.le⟩ hq.2
    rwa [c_derivative_zero] at hmono

theorem lambdaDerivativeFormula_pos_global {q : ℝ}
    (hq : q ∈ Ioo c qSoft) :
    0 < LambdaDerivativeFormula q := by
  by_cases hlocal : q ≤ (localFinish : ℝ)
  · have hmono := strictMonoOn_lambdaDerivativeFormula_local
      ⟨c_mem_local.1.le, c_mem_local.2.le⟩
      ⟨c_mem_local.1.le.trans hq.1.le, hlocal⟩ hq.1
    rwa [c_derivative_zero] at hmono
  by_cases hregular : q ≤ (1 / 10 : ℝ)
  · have hfinish : q ≤ (positiveFinish : ℝ) := by
      norm_num [positiveFinish] at hregular ⊢
      exact hregular
    exact lambdaDerivativeFormula_pos_regular
      ⟨(lt_of_not_ge hlocal).le, hfinish⟩
  · exact OneCutSoftCandidates.lambdaDerivativeFormula_pos_soft
      (lt_of_not_ge hregular).le hq.2

end

end Erdos1038
