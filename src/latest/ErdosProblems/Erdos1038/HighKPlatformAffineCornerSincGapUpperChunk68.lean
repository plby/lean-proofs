import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk68
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk68
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 68. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_068 : Rat := -531529097118 / 1000000000000

theorem gapUpperCheck_068 : EvalUpper ![qOuter_068, rOuter_068]
    (sincGapE2 scalarTrigDoubles) gapUpper_068 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
