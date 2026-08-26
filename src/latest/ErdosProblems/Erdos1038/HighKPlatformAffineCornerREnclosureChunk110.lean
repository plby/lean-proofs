import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine rOuter semantic enclosure for cell 110. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineTableData
open Erdos1038.HighKPlatformAffineSemanticCorner

def rOuter_110 : RatInterval :=
  ⟨1599804229955 / 1000000000000,
    1661375018213 / 1000000000000⟩

theorem rEnclosed_110 : EvalEnclosed
    (data ⟨110, by decide⟩).boxes
    (rmaxE scalarSqrtSteps .affine) rOuter_110 := by
  exact evalEnclosed_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
