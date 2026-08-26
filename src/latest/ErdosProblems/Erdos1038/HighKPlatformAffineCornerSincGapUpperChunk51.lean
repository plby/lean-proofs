import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk51
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk51
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 51. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_051 : Rat := -534297276641 / 1000000000000

theorem gapUpperCheck_051 : EvalUpper ![qOuter_051, rOuter_051]
    (sincGapE2 scalarTrigDoubles) gapUpper_051 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
