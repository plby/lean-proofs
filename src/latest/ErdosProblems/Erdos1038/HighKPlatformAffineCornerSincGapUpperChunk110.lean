import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk110
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk110
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 110. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_110 : Rat := -520964398541 / 1000000000000

theorem gapUpperCheck_110 : EvalUpper ![qOuter_110, rOuter_110]
    (sincGapE2 scalarTrigDoubles) gapUpper_110 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
