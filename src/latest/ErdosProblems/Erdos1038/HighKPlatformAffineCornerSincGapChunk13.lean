import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk13
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk13
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk13
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 13. -/

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

def sincGapLower_013 : Rat := 287999 / 1000000

theorem sincGap_013 : UniformLower (data ⟨13, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_013 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_013) (rOuter := rOuter_013)
      (gapUpper := gapUpper_013)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_013
  · exact rEnclosed_013
  · exact gapUpperCheck_013
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
