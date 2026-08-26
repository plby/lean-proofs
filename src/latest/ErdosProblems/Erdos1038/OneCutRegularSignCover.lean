import ErdosProblems.Erdos1038.OneCutTailQCertificate

/-!
# Exact derivative signs away from the stationary and soft-edge charts
-/

namespace Erdos1038

noncomputable section

namespace OneCutTailCertificate
namespace OneCutRegularSignCover

def negativeStart : Rat := tailQ
def negativeFinish : Rat := 240189709838717 / 10 ^ 16
def positiveStart : Rat := 274644706879705 / 10 ^ 16
def positiveFinish : Rat := 1 / 10

theorem lambdaDerivativeFormula_neg_regular {q : ℝ}
    (hq : (negativeStart : ℝ) ≤ q ∧ q ≤ (negativeFinish : ℝ)) :
    LambdaDerivativeFormula q < 0 := by
  exact TailQBox.derivative_negative_of_cover
    OneCutTailQCandidates.negativeCover_certified hq

theorem lambdaDerivativeFormula_pos_regular {q : ℝ}
    (hq : (positiveStart : ℝ) ≤ q ∧ q ≤ (positiveFinish : ℝ)) :
    0 < LambdaDerivativeFormula q := by
  exact TailQBox.derivative_positive_of_cover
    OneCutTailQCandidates.positiveCover_certified hq

end OneCutRegularSignCover
end OneCutTailCertificate

end

end Erdos1038
