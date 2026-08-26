import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk77
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk77
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 77. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_077 : Rat := -529700068045 / 1000000000000

theorem gapUpperCheck_077 : EvalUpper ![qOuter_077, rOuter_077]
    (sincGapE2 scalarTrigDoubles) gapUpper_077 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
