import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk189
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk189
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 189. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_189 : Rat := -489620343229 / 1000000000000

theorem gapUpperCheck_189 : EvalUpper ![qOuter_189, rOuter_189]
    (sincGapE2 scalarTrigDoubles) gapUpper_189 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
