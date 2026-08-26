import ErdosProblems.Erdos1038.OneCutGlobalSigns
import ErdosProblems.Erdos1038.OneCutSoftEndpointValue

/-!
# Closed exact one-cut certificate
-/

namespace Erdos1038

noncomputable section

open OneCutStationaryPoint
open OneCutSoftEndpointValue

theorem oneCut_global_certificate :
    (∃! q : ℝ, IsLambdaMinimizer q) ∧
      IsLambdaMinimizer qStar ∧
      (25715536866527 / 10 ^ 15 : ℝ) < qStar ∧
      qStar < (25715536866528 / 10 ^ 15 : ℝ) ∧
      (1834430475762661 / 10 ^ 15 : ℝ) < L ∧
      L < (1834430475762662 / 10 ^ 15 : ℝ) := by
  apply oneCut_global_certificate_reduction c_decimal_box
    (fun q hq ↦ lambdaDerivativeFormula_neg_global hq)
    (fun q hq ↦ lambdaDerivativeFormula_pos_global hq)
  · exact c_lambda_decimal_box.2.trans lambdaUpper_lt_Lambda_qSoft
  · exact c_lambda_decimal_box

end

end Erdos1038
