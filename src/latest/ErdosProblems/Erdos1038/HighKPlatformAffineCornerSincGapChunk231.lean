import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk231
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk231
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk231
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 231. -/

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

def sincGapLower_231 : Rat := 218999 / 1000000

theorem sincGap_231 : UniformLower (data ⟨231, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_231 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_231) (rOuter := rOuter_231)
      (gapUpper := gapUpper_231)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_231
  · exact rEnclosed_231
  · exact gapUpperCheck_231
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
