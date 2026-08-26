import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk240
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk240
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 240. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_240 : Rat := -463676426815 / 1000000000000

theorem gapUpperCheck_240 : EvalUpper ![qOuter_240, rOuter_240]
    (sincGapE2 scalarTrigDoubles) gapUpper_240 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
