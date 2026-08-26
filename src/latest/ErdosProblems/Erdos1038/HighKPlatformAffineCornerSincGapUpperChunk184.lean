import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk184
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk184
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 184. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_184 : Rat := -491954327749 / 1000000000000

theorem gapUpperCheck_184 : EvalUpper ![qOuter_184, rOuter_184]
    (sincGapE2 scalarTrigDoubles) gapUpper_184 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
