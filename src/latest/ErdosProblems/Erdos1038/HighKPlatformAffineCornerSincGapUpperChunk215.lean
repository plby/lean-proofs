import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk215
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk215
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 215. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_215 : Rat := -476857470320 / 1000000000000

theorem gapUpperCheck_215 : EvalUpper ![qOuter_215, rOuter_215]
    (sincGapE2 scalarTrigDoubles) gapUpper_215 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
