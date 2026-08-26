import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk221
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk221
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 221. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_221 : Rat := -473771520894 / 1000000000000

theorem gapUpperCheck_221 : EvalUpper ![qOuter_221, rOuter_221]
    (sincGapE2 scalarTrigDoubles) gapUpper_221 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
