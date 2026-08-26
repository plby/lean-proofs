import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk36
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk36
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 36. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_036 : Rat := -535993213851 / 1000000000000

theorem gapUpperCheck_036 : EvalUpper ![qOuter_036, rOuter_036]
    (sincGapE2 scalarTrigDoubles) gapUpper_036 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
