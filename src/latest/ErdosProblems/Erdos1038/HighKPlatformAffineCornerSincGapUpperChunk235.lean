import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk235
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk235
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 235. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_235 : Rat := -466379328748 / 1000000000000

theorem gapUpperCheck_235 : EvalUpper ![qOuter_235, rOuter_235]
    (sincGapE2 scalarTrigDoubles) gapUpper_235 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
