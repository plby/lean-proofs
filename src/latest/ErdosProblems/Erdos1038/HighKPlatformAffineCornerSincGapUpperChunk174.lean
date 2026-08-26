import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk174
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk174
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 174. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_174 : Rat := -496497455336 / 1000000000000

theorem gapUpperCheck_174 : EvalUpper ![qOuter_174, rOuter_174]
    (sincGapE2 scalarTrigDoubles) gapUpper_174 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
