import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk20
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk20
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sinc-gap upper check for cell 20. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineSemanticCorner

def gapUpper_020 : Rat := -537053451837 / 1000000000000

theorem gapUpperCheck_020 : EvalUpper ![qOuter_020, rOuter_020]
    (sincGapE2 scalarTrigDoubles) gapUpper_020 := by
  exact evalUpper_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
