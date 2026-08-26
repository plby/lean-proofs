import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk146
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk146
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk146
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 146. -/

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

def sincGapLower_146 : Rat := 257999 / 1000000

theorem sincGap_146 : UniformLower (data ⟨146, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_146 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_146) (rOuter := rOuter_146)
      (gapUpper := gapUpper_146)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_146
  · exact rEnclosed_146
  · exact gapUpperCheck_146
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
