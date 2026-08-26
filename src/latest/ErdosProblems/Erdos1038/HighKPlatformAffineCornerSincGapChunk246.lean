import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk246
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk246
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk246
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 246. -/

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

def sincGapLower_246 : Rat := 210999 / 1000000

theorem sincGap_246 : UniformLower (data ⟨246, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_246 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_246) (rOuter := rOuter_246)
      (gapUpper := gapUpper_246)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_246
  · exact rEnclosed_246
  · exact gapUpperCheck_246
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
