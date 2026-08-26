import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk136
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk136
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 136. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_136 : Rat := -512082128535 / 1000000000000

theorem gapUpperCheck_136 : EvalUpper ![qOuter_136, rOuter_136]
    (sincGapE2 scalarTrigDoubles) gapUpper_136 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
