import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk220
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk220
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 220. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_220 : Rat := -474289340485 / 1000000000000

theorem gapUpperCheck_220 : EvalUpper ![qOuter_220, rOuter_220]
    (sincGapE2 scalarTrigDoubles) gapUpper_220 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
