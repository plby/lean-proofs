import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk241
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk241
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 241. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_241 : Rat := -463131981958 / 1000000000000

theorem gapUpperCheck_241 : EvalUpper ![qOuter_241, rOuter_241]
    (sincGapE2 scalarTrigDoubles) gapUpper_241 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
