import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk247
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk247
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 247. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_247 : Rat := -459838673053 / 1000000000000

theorem gapUpperCheck_247 : EvalUpper ![qOuter_247, rOuter_247]
    (sincGapE2 scalarTrigDoubles) gapUpper_247 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
