import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk106
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk106
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 106. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_106 : Rat := -522183268583 / 1000000000000

theorem gapUpperCheck_106 : EvalUpper ![qOuter_106, rOuter_106]
    (sincGapE2 scalarTrigDoubles) gapUpper_106 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
