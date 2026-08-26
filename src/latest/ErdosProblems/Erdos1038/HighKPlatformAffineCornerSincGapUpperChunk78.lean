import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk78
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk78
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 78. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_078 : Rat := -529481576203 / 1000000000000

theorem gapUpperCheck_078 : EvalUpper ![qOuter_078, rOuter_078]
    (sincGapE2 scalarTrigDoubles) gapUpper_078 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
