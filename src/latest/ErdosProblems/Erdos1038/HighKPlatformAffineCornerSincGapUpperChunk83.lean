import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk83
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk83
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 83. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_083 : Rat := -528344044412 / 1000000000000

theorem gapUpperCheck_083 : EvalUpper ![qOuter_083, rOuter_083]
    (sincGapE2 scalarTrigDoubles) gapUpper_083 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
