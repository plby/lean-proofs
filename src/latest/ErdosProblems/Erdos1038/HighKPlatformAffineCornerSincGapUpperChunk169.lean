import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk169
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk169
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 169. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_169 : Rat := -498704311565 / 1000000000000

theorem gapUpperCheck_169 : EvalUpper ![qOuter_169, rOuter_169]
    (sincGapE2 scalarTrigDoubles) gapUpper_169 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
