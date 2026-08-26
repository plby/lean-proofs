import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk262
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk262
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 262. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_262 : Rat := -451410921669 / 1000000000000

theorem gapUpperCheck_262 : EvalUpper ![qOuter_262, rOuter_262]
    (sincGapE2 scalarTrigDoubles) gapUpper_262 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
