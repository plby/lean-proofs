import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk261
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk261
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk261
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 261. -/

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

def sincGapLower_261 : Rat := 203999 / 1000000

theorem sincGap_261 : UniformLower (data ⟨261, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_261 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_261) (rOuter := rOuter_261)
      (gapUpper := gapUpper_261)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_261
  · exact rEnclosed_261
  · exact gapUpperCheck_261
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
