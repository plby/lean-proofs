import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk237
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk237
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk237
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 237. -/

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

def sincGapLower_237 : Rat := 215999 / 1000000

theorem sincGap_237 : UniformLower (data ⟨237, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_237 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_237) (rOuter := rOuter_237)
      (gapUpper := gapUpper_237)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_237
  · exact rEnclosed_237
  · exact gapUpperCheck_237
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
