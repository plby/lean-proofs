import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk35
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk35
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 35. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_035 : Rat := -536081839735 / 1000000000000

theorem gapUpperCheck_035 : EvalUpper ![qOuter_035, rOuter_035]
    (sincGapE2 scalarTrigDoubles) gapUpper_035 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
