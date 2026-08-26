import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk172
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk172
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 172. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_172 : Rat := -497385489313 / 1000000000000

theorem gapUpperCheck_172 : EvalUpper ![qOuter_172, rOuter_172]
    (sincGapE2 scalarTrigDoubles) gapUpper_172 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
