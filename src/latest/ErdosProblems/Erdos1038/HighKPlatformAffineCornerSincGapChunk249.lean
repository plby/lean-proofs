import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk249
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk249
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk249
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 249. -/

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

def sincGapLower_249 : Rat := 209999 / 1000000

theorem sincGap_249 : UniformLower (data ⟨249, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_249 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_249) (rOuter := rOuter_249)
      (gapUpper := gapUpper_249)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_249
  · exact rEnclosed_249
  · exact gapUpperCheck_249
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
