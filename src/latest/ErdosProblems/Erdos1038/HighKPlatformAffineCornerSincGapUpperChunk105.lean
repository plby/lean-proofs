import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk105
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk105
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 105. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_105 : Rat := -522481437595 / 1000000000000

theorem gapUpperCheck_105 : EvalUpper ![qOuter_105, rOuter_105]
    (sincGapE2 scalarTrigDoubles) gapUpper_105 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
