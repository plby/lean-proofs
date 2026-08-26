import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk109
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk109
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 109. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_109 : Rat := -521273013956 / 1000000000000

theorem gapUpperCheck_109 : EvalUpper ![qOuter_109, rOuter_109]
    (sincGapE2 scalarTrigDoubles) gapUpper_109 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
