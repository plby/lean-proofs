import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk225
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk225
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk225
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 225. -/

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

def sincGapLower_225 : Rat := 221999 / 1000000

theorem sincGap_225 : UniformLower (data ⟨225, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_225 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_225) (rOuter := rOuter_225)
      (gapUpper := gapUpper_225)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_225
  · exact rEnclosed_225
  · exact gapUpperCheck_225
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
