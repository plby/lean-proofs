import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk161
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk161
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 161. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_161 : Rat := -502141630183 / 1000000000000

theorem gapUpperCheck_161 : EvalUpper ![qOuter_161, rOuter_161]
    (sincGapE2 scalarTrigDoubles) gapUpper_161 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
