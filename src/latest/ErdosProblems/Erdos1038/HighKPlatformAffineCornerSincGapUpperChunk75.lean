import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk75
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk75
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 75. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_075 : Rat := -530127954546 / 1000000000000

theorem gapUpperCheck_075 : EvalUpper ![qOuter_075, rOuter_075]
    (sincGapE2 scalarTrigDoubles) gapUpper_075 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
