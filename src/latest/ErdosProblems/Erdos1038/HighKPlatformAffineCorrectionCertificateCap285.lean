import ErdosProblems.Erdos1038.HighKPlatformAffineCorrectionComponents
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated globally reusable affine correction check at cap 285 / 100. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCorrectionCertificates

open Erdos1038 HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineCornerComponents
open Erdos1038.HighKPlatformAffineCorrectionComponents

def cap285CorrectionLower : Rat := 38009938999 / 500000000000

theorem cap285CorrectionGlobal : EvalLower correctionBoxes
    (correctionE scalarLogTerms scalarTrigDoubles
      scalarFourierTerms (285 / 100)) cap285CorrectionLower := by
  exact evalLower_of_check (by kernel_decide)

theorem cap285Correction (d : Data) : EvalLower d.boxes
    (circleCorrectionLowerE scalarLogTerms scalarTrigDoubles
      scalarFourierTerms (.rat (285 / 100)) piE)
    cap285CorrectionLower :=
  evalLower_correctionE_of_global d cap285CorrectionGlobal

end Erdos1038.HighKPlatformAffineCorrectionCertificates
