import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk6
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk6
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk6
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 6. -/

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineTableData
open Erdos1038.HighKPlatformAffineCornerComponents
open Erdos1038.HighKPlatformAffineSemanticCorner

def sincGapLower_006 : Rat := 287999 / 1000000

theorem sincGap_006 : UniformLower (data ⟨6, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_006 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_006) (rOuter := rOuter_006)
      (gapUpper := gapUpper_006)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_006
  · exact rEnclosed_006
  · exact gapUpperCheck_006
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
