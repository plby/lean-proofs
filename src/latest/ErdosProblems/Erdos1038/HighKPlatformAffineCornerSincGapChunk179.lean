import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk179
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk179
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk179
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 179. -/

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

def sincGapLower_179 : Rat := 243999 / 1000000

theorem sincGap_179 : UniformLower (data ⟨179, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_179 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_179) (rOuter := rOuter_179)
      (gapUpper := gapUpper_179)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_179
  · exact rEnclosed_179
  · exact gapUpperCheck_179
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
