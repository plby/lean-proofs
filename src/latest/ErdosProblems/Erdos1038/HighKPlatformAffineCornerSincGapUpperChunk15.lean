import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk15
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk15
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 15. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_015 : Rat := -537228707082 / 1000000000000

theorem gapUpperCheck_015 : EvalUpper ![qOuter_015, rOuter_015]
    (sincGapE2 scalarTrigDoubles) gapUpper_015 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
