import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk4
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk4
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 4. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_004 : Rat := -537339014313 / 1000000000000

theorem gapUpperCheck_004 : EvalUpper ![qOuter_004, rOuter_004]
    (sincGapE2 scalarTrigDoubles) gapUpper_004 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
