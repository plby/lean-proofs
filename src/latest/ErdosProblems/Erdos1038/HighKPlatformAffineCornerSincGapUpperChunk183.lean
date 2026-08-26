import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk183
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk183
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 183. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_183 : Rat := -492416210034 / 1000000000000

theorem gapUpperCheck_183 : EvalUpper ![qOuter_183, rOuter_183]
    (sincGapE2 scalarTrigDoubles) gapUpper_183 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
