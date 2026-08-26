import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk256
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk256
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 256. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_256 : Rat := -454814760887 / 1000000000000

theorem gapUpperCheck_256 : EvalUpper ![qOuter_256, rOuter_256]
    (sincGapE2 scalarTrigDoubles) gapUpper_256 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
