import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk245
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk245
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 245. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_245 : Rat := -460941485366 / 1000000000000

theorem gapUpperCheck_245 : EvalUpper ![qOuter_245, rOuter_245]
    (sincGapE2 scalarTrigDoubles) gapUpper_245 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
