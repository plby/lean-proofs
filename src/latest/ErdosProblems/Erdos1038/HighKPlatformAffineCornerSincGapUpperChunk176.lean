import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk176
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk176
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 176. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_176 : Rat := -495602457193 / 1000000000000

theorem gapUpperCheck_176 : EvalUpper ![qOuter_176, rOuter_176]
    (sincGapE2 scalarTrigDoubles) gapUpper_176 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
