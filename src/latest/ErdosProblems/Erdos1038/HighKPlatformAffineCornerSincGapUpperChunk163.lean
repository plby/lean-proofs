import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk163
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk163
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 163. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_163 : Rat := -501293335080 / 1000000000000

theorem gapUpperCheck_163 : EvalUpper ![qOuter_163, rOuter_163]
    (sincGapE2 scalarTrigDoubles) gapUpper_163 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
