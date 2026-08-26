import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk30
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk30
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 30. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_030 : Rat := -536479971248 / 1000000000000

theorem gapUpperCheck_030 : EvalUpper ![qOuter_030, rOuter_030]
    (sincGapE2 scalarTrigDoubles) gapUpper_030 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
