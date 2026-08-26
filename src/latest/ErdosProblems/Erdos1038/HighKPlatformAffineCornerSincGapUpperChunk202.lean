import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk202
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk202
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 202. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_202 : Rat := -483366382530 / 1000000000000

theorem gapUpperCheck_202 : EvalUpper ![qOuter_202, rOuter_202]
    (sincGapE2 scalarTrigDoubles) gapUpper_202 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
