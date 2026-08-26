import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk141
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk141
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 141. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_141 : Rat := -510196764607 / 1000000000000

theorem gapUpperCheck_141 : EvalUpper ![qOuter_141, rOuter_141]
    (sincGapE2 scalarTrigDoubles) gapUpper_141 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
