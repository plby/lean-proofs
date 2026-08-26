import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk65
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk65
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 65. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_065 : Rat := -532083207978 / 1000000000000

theorem gapUpperCheck_065 : EvalUpper ![qOuter_065, rOuter_065]
    (sincGapE2 scalarTrigDoubles) gapUpper_065 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
