import ErdosProblems.Erdos1038.Statement
import ErdosProblems.Erdos1038.SoftEdgePackage
import ErdosProblems.Erdos1038.ExteriorPackage
import ErdosProblems.Erdos1038.LambdaAnalysis
import ErdosProblems.Erdos1038.HighKLowerBridge
import ErdosProblems.Erdos1038.TaoUpperCaseAssembly
import ErdosProblems.Erdos1038.RecoveryPositiveAssembly
import ErdosProblems.Erdos1038.RecoveryPositiveLimit

/-!
# Final assembly reduction

This theorem records the exact remaining certificate leaves after the
unconditional soft-edge/exterior packages and the completed upper/lower
order reductions.
-/

open scoped ENNReal
open Filter Polynomial Set Topology

namespace Erdos1038

noncomputable section

theorem mainTheorem_of_remaining_certificates
    {c : ℝ}
    (hcbox : (qStarLowerRat : ℝ) < c ∧ c < (qStarUpperRat : ℝ))
    (hneg : ∀ q ∈ Ioo (0 : ℝ) c, LambdaDerivativeFormula q < 0)
    (hpos : ∀ q ∈ Ioo c qSoft, 0 < LambdaDerivativeFormula q)
    (hend : Lambda c < Lambda qSoft)
    (hLbox : (lambdaLowerRat : ℝ) < Lambda c ∧
      Lambda c < (lambdaUpperRat : ℝ))
    (hhigh : HighKEndpointStrictLowerBound)
    (hrecovery : ∃ f : ℕ → AdmissiblePolynomial,
      Tendsto (fun n ↦ sublevelVolume (f n).1) atTop
        (𝓝 (ENNReal.ofReal L))) :
    MainTheorem := by
  obtain ⟨hlambdaUnique, hlambdaMin, hqStarLower, hqStarUpper,
      hLLower, hLUpper⟩ :=
    oneCut_global_certificate_reduction hcbox hneg hpos hend hLbox
  have hLtwo : L < 2 := by
    exact hLUpper.trans (by norm_num)
  obtain ⟨hinfimum, hlowerStrict⟩ :=
    mainTheorem_lower_clauses_of_highKEndpointStrictLowerBound
      hLtwo hhigh hrecovery
  obtain ⟨hsupremum, hextremizers, hequality⟩ :=
    mainTheorem_upper_clauses
  obtain ⟨hsoftUnique, hsoftRoot, hsoftLower, hsoftUpper⟩ :=
    mainTheorem_softEdge_clause
  exact ⟨hsoftUnique, hsoftRoot, hsoftLower, hsoftUpper,
    mainTheorem_exterior_clause,
    hlambdaUnique, hlambdaMin, hqStarLower, hqStarUpper,
    hLLower, hLUpper, hinfimum, hsupremum, hlowerStrict,
    hextremizers, hequality⟩

/-- Final reduction using the concrete positive-buffer recovery certificate
from Section 9 instead of an abstract recovering polynomial sequence. -/
theorem mainTheorem_of_remaining_positiveBuffer_certificates
    {c : ℝ}
    (hcbox : (qStarLowerRat : ℝ) < c ∧ c < (qStarUpperRat : ℝ))
    (hneg : ∀ q ∈ Ioo (0 : ℝ) c, LambdaDerivativeFormula q < 0)
    (hpos : ∀ q ∈ Ioo c qSoft, 0 < LambdaDerivativeFormula q)
    (hend : Lambda c < Lambda qSoft)
    (hLbox : (lambdaLowerRat : ℝ) < Lambda c ∧
      Lambda c < (lambdaUpperRat : ℝ))
    (hhigh : HighKEndpointStrictLowerBound)
    (hrecovery : PositiveBufferRecoveryCertificate) :
    MainTheorem := by
  apply mainTheorem_of_remaining_certificates
    hcbox hneg hpos hend hLbox hhigh
  exact mainTheorem_recovery_clause_of_positiveBufferRecoveryCertificate
    hrecovery

/-- Final reduction with recovery discharged automatically from the exact
one-cut certificate.  Thus the only genuinely independent remaining leaves
are the five one-cut sign/enclosure facts and the high-k endpoint bound. -/
theorem mainTheorem_of_remaining_oneCut_highK_certificates
    {c : ℝ}
    (hcbox : (qStarLowerRat : ℝ) < c ∧ c < (qStarUpperRat : ℝ))
    (hneg : ∀ q ∈ Ioo (0 : ℝ) c, LambdaDerivativeFormula q < 0)
    (hpos : ∀ q ∈ Ioo c qSoft, 0 < LambdaDerivativeFormula q)
    (hend : Lambda c < Lambda qSoft)
    (hLbox : (lambdaLowerRat : ℝ) < Lambda c ∧
      Lambda c < (lambdaUpperRat : ℝ))
    (hhigh : HighKEndpointStrictLowerBound) :
    MainTheorem := by
  apply mainTheorem_of_remaining_positiveBuffer_certificates
    hcbox hneg hpos hend hLbox hhigh
  exact positiveBufferRecoveryCertificate_of_oneCut_global_certificate
    hcbox hneg hpos hend hLbox

end

end Erdos1038
