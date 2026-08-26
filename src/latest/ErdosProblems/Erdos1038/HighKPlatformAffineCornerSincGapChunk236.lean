import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk236
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk236
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk236
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 236. -/

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

def sincGapLower_236 : Rat := 216999 / 1000000

theorem sincGap_236 : UniformLower (data ⟨236, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_236 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_236) (rOuter := rOuter_236)
      (gapUpper := gapUpper_236)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_236
  · exact rEnclosed_236
  · exact gapUpperCheck_236
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
