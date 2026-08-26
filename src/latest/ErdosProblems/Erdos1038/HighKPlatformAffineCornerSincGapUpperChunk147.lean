import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk147
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk147
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 147. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_147 : Rat := -507864568288 / 1000000000000

theorem gapUpperCheck_147 : EvalUpper ![qOuter_147, rOuter_147]
    (sincGapE2 scalarTrigDoubles) gapUpper_147 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
