import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk144
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk144
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 144. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_144 : Rat := -509040020717 / 1000000000000

theorem gapUpperCheck_144 : EvalUpper ![qOuter_144, rOuter_144]
    (sincGapE2 scalarTrigDoubles) gapUpper_144 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
