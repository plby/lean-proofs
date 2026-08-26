import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk41
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk41
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk41
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 41. -/

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

def sincGapLower_041 : Rat := 285999 / 1000000

theorem sincGap_041 : UniformLower (data ⟨41, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_041 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_041) (rOuter := rOuter_041)
      (gapUpper := gapUpper_041)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_041
  · exact rEnclosed_041
  · exact gapUpperCheck_041
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
