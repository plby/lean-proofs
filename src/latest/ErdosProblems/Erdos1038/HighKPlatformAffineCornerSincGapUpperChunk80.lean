import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk80
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk80
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 80. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_080 : Rat := -529035545149 / 1000000000000

theorem gapUpperCheck_080 : EvalUpper ![qOuter_080, rOuter_080]
    (sincGapE2 scalarTrigDoubles) gapUpper_080 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
