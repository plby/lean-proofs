import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk211
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk211
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 211. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_211 : Rat := -478886442488 / 1000000000000

theorem gapUpperCheck_211 : EvalUpper ![qOuter_211, rOuter_211]
    (sincGapE2 scalarTrigDoubles) gapUpper_211 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
