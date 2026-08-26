import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk258
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk258
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 258. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_258 : Rat := -453684935040 / 1000000000000

theorem gapUpperCheck_258 : EvalUpper ![qOuter_258, rOuter_258]
    (sincGapE2 scalarTrigDoubles) gapUpper_258 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
