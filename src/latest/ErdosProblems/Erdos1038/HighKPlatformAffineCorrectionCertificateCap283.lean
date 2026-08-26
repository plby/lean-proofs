import ErdosProblems.Erdos1038.HighKPlatformAffineCorrectionComponents
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated globally reusable affine correction check at cap 283 / 100. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCorrectionCertificates

open Erdos1038 HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineCornerComponents
open Erdos1038.HighKPlatformAffineCorrectionComponents

def cap283CorrectionLower : Rat := 2515089717 / 31250000000

theorem cap283CorrectionGlobal : EvalLower correctionBoxes
    (correctionE scalarLogTerms scalarTrigDoubles
      scalarFourierTerms (283 / 100)) cap283CorrectionLower := by
  exact evalLower_of_check (by kernel_decide)

theorem cap283Correction (d : Data) : EvalLower d.boxes
    (circleCorrectionLowerE scalarLogTerms scalarTrigDoubles
      scalarFourierTerms (.rat (283 / 100)) piE)
    cap283CorrectionLower :=
  evalLower_correctionE_of_global d cap283CorrectionGlobal

end Erdos1038.HighKPlatformAffineCorrectionCertificates
