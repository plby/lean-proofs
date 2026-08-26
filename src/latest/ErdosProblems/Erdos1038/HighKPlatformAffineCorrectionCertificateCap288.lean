import ErdosProblems.Erdos1038.HighKPlatformAffineCorrectionComponents
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated globally reusable affine correction check at cap 288 / 100. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCorrectionCertificates

open Erdos1038 HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineCornerComponents
open Erdos1038.HighKPlatformAffineCorrectionComponents

def cap288CorrectionLower : Rat := 69183511613 / 1000000000000

theorem cap288CorrectionGlobal : EvalLower correctionBoxes
    (correctionE scalarLogTerms scalarTrigDoubles
      scalarFourierTerms (288 / 100)) cap288CorrectionLower := by
  exact evalLower_of_check (by kernel_decide)

theorem cap288Correction (d : Data) : EvalLower d.boxes
    (circleCorrectionLowerE scalarLogTerms scalarTrigDoubles
      scalarFourierTerms (.rat (288 / 100)) piE)
    cap288CorrectionLower :=
  evalLower_correctionE_of_global d cap288CorrectionGlobal

end Erdos1038.HighKPlatformAffineCorrectionCertificates
