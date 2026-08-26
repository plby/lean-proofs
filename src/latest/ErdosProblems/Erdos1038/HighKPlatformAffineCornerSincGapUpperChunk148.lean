import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk148
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk148
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 148. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_148 : Rat := -507468652712 / 1000000000000

theorem gapUpperCheck_148 : EvalUpper ![qOuter_148, rOuter_148]
    (sincGapE2 scalarTrigDoubles) gapUpper_148 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
