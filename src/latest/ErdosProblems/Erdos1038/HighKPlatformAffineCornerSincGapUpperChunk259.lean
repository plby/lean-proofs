import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk259
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk259
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 259. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_259 : Rat := -453118220785 / 1000000000000

theorem gapUpperCheck_259 : EvalUpper ![qOuter_259, rOuter_259]
    (sincGapE2 scalarTrigDoubles) gapUpper_259 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
