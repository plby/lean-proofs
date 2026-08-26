import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk143
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk143
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 143. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_143 : Rat := -509427698118 / 1000000000000

theorem gapUpperCheck_143 : EvalUpper ![qOuter_143, rOuter_143]
    (sincGapE2 scalarTrigDoubles) gapUpper_143 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
