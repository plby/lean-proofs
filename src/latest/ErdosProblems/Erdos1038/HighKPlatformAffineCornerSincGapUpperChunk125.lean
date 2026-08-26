import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk125
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk125
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 125. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_125 : Rat := -516035082896 / 1000000000000

theorem gapUpperCheck_125 : EvalUpper ![qOuter_125, rOuter_125]
    (sincGapE2 scalarTrigDoubles) gapUpper_125 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
