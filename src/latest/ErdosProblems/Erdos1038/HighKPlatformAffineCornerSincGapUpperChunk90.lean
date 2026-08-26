import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk90
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk90
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 90. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_090 : Rat := -526627424280 / 1000000000000

theorem gapUpperCheck_090 : EvalUpper ![qOuter_090, rOuter_090]
    (sincGapE2 scalarTrigDoubles) gapUpper_090 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
