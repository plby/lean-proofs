import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk155
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk155
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 155. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_155 : Rat := -504641154016 / 1000000000000

theorem gapUpperCheck_155 : EvalUpper ![qOuter_155, rOuter_155]
    (sincGapE2 scalarTrigDoubles) gapUpper_155 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
