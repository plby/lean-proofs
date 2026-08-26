import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk11
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk11
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 11. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_011 : Rat := -537314020654 / 1000000000000

theorem gapUpperCheck_011 : EvalUpper ![qOuter_011, rOuter_011]
    (sincGapE2 scalarTrigDoubles) gapUpper_011 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
