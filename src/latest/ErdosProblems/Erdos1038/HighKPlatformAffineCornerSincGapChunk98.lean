import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk98
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk98
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk98
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 98. -/

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

def sincGapLower_098 : Rat := 274999 / 1000000

theorem sincGap_098 : UniformLower (data ⟨98, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_098 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_098) (rOuter := rOuter_098)
      (gapUpper := gapUpper_098)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_098
  · exact rEnclosed_098
  · exact gapUpperCheck_098
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
