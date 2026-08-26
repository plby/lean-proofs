import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk119
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk119
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 119. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_119 : Rat := -518072944411 / 1000000000000

theorem gapUpperCheck_119 : EvalUpper ![qOuter_119, rOuter_119]
    (sincGapE2 scalarTrigDoubles) gapUpper_119 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
