import ErdosProblems.Erdos1038.FinalAssemblyReduction
import ErdosProblems.Erdos1038.OneCutGlobalCertificate

/-!
# Final assembly after the exact one-cut certificate

The 179-box soft-chart certificate now closes every one-cut leaf.  This
module records that fact at the final theorem boundary: the sole remaining
input is the concrete high-ratio endpoint theorem.
-/

set_option warningAsError false

open Set

namespace Erdos1038

noncomputable section

/-- The completed exact one-cut certificate reduces `MainTheorem` to the
single high-`k` endpoint assertion. -/
theorem mainTheorem_of_highKEndpointStrictLowerBound
    (hhigh : HighKEndpointStrictLowerBound) : MainTheorem := by
  apply mainTheorem_of_remaining_oneCut_highK_certificates
    OneCutStationaryPoint.c_decimal_box
  · intro q hq
    exact lambdaDerivativeFormula_neg_global hq
  · intro q hq
    exact lambdaDerivativeFormula_pos_global hq
  · exact OneCutStationaryPoint.c_lambda_decimal_box.2.trans
      OneCutSoftEndpointValue.lambdaUpper_lt_Lambda_qSoft
  · exact OneCutStationaryPoint.c_lambda_decimal_box
  · exact hhigh

end

end Erdos1038
