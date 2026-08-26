import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk171
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk171
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 171. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_171 : Rat := -497826870291 / 1000000000000

theorem gapUpperCheck_171 : EvalUpper ![qOuter_171, rOuter_171]
    (sincGapE2 scalarTrigDoubles) gapUpper_171 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
