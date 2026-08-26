import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk10
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk10
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk10
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 10. -/

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

def sincGapLower_010 : Rat := 287999 / 1000000

theorem sincGap_010 : UniformLower (data ⟨10, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_010 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_010) (rOuter := rOuter_010)
      (gapUpper := gapUpper_010)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_010
  · exact rEnclosed_010
  · exact gapUpperCheck_010
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
