import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk29
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk29
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 29. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_029 : Rat := -536550648209 / 1000000000000

theorem gapUpperCheck_029 : EvalUpper ![qOuter_029, rOuter_029]
    (sincGapE2 scalarTrigDoubles) gapUpper_029 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
