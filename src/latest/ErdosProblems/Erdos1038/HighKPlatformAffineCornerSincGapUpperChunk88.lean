import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk88
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk88
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 88. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_088 : Rat := -527132450064 / 1000000000000

theorem gapUpperCheck_088 : EvalUpper ![qOuter_088, rOuter_088]
    (sincGapE2 scalarTrigDoubles) gapUpper_088 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
