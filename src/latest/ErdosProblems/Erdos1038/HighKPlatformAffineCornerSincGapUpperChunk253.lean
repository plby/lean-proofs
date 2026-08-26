import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk253
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk253
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 253. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_253 : Rat := -456500428171 / 1000000000000

theorem gapUpperCheck_253 : EvalUpper ![qOuter_253, rOuter_253]
    (sincGapE2 scalarTrigDoubles) gapUpper_253 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
