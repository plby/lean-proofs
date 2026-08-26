import ErdosProblems.Erdos1038.HighKPlatformAffineCorrectionComponents
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated globally reusable affine correction check at cap 297 / 100. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCorrectionCertificates

open Erdos1038 HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineCornerComponents
open Erdos1038.HighKPlatformAffineCorrectionComponents

def cap297CorrectionLower : Rat := 47569445329 / 1000000000000

theorem cap297CorrectionGlobal : EvalLower correctionBoxes
    (correctionE scalarLogTerms scalarTrigDoubles
      scalarFourierTerms (297 / 100)) cap297CorrectionLower := by
  exact evalLower_of_check (by kernel_decide)

theorem cap297Correction (d : Data) : EvalLower d.boxes
    (circleCorrectionLowerE scalarLogTerms scalarTrigDoubles
      scalarFourierTerms (.rat (297 / 100)) piE)
    cap297CorrectionLower :=
  evalLower_correctionE_of_global d cap297CorrectionGlobal

end Erdos1038.HighKPlatformAffineCorrectionCertificates
