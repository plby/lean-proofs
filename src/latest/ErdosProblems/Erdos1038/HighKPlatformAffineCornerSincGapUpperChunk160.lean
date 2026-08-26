import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk160
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk160
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 160. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_160 : Rat := -502562970426 / 1000000000000

theorem gapUpperCheck_160 : EvalUpper ![qOuter_160, rOuter_160]
    (sincGapE2 scalarTrigDoubles) gapUpper_160 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
