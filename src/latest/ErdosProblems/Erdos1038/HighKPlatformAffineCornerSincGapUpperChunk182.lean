import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk182
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk182
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 182. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_182 : Rat := -492876434395 / 1000000000000

theorem gapUpperCheck_182 : EvalUpper ![qOuter_182, rOuter_182]
    (sincGapE2 scalarTrigDoubles) gapUpper_182 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
