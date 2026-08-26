import ErdosProblems.Erdos1038.OneCutSoftCandidatesCertificate

/-!
# Exact positivity on the soft edge
-/

open Set

namespace Erdos1038

noncomputable section

namespace OneCutSoftCandidates

theorem lambdaDerivativeFormula_pos_soft {q : ℝ}
    (hq : (1 / 10 : ℝ) ≤ q) (hqs : q < qSoft) :
    0 < LambdaDerivativeFormula q := by
  apply SoftBox.derivative_positive_of_cover (by norm_num)
    positiveCover_certified
  · constructor
    · norm_num at hq ⊢
      exact hq
    · exact hqs.le.trans qSoft_lt_qSoftUpper.le
  · exact hqs

end OneCutSoftCandidates

end

end Erdos1038
