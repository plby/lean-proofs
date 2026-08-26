import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk128
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk128
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 128. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_128 : Rat := -514984310934 / 1000000000000

theorem gapUpperCheck_128 : EvalUpper ![qOuter_128, rOuter_128]
    (sincGapE2 scalarTrigDoubles) gapUpper_128 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
