import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk38
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk38
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk38
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 38. -/

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

def sincGapLower_038 : Rat := 286999 / 1000000

theorem sincGap_038 : UniformLower (data ⟨38, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_038 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_038) (rOuter := rOuter_038)
      (gapUpper := gapUpper_038)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_038
  · exact rEnclosed_038
  · exact gapUpperCheck_038
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
