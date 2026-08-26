import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk132
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk132
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 132. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_132 : Rat := -513551155544 / 1000000000000

theorem gapUpperCheck_132 : EvalUpper ![qOuter_132, rOuter_132]
    (sincGapE2 scalarTrigDoubles) gapUpper_132 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
