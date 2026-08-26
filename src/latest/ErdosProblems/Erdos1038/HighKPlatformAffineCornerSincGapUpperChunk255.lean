import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk255
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk255
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 255. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_255 : Rat := -455377863702 / 1000000000000

theorem gapUpperCheck_255 : EvalUpper ![qOuter_255, rOuter_255]
    (sincGapE2 scalarTrigDoubles) gapUpper_255 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
