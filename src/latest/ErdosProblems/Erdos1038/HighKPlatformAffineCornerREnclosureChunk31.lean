import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine rOuter semantic enclosure for cell 31. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineTableData
open Erdos1038.HighKPlatformAffineSemanticCorner

def rOuter_031 : RatInterval :=
  ⟨1556566711371 / 1000000000000,
    1653517931582 / 1000000000000⟩

theorem rEnclosed_031 : EvalEnclosed
    (data ⟨31, by decide⟩).boxes
    (rmaxE scalarSqrtSteps .affine) rOuter_031 := by
  exact evalEnclosed_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
