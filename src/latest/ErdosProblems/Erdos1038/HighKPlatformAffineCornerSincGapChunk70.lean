import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk70
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk70
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk70
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 70. -/

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

def sincGapLower_070 : Rat := 281999 / 1000000

theorem sincGap_070 : UniformLower (data ⟨70, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_070 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_070) (rOuter := rOuter_070)
      (gapUpper := gapUpper_070)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_070
  · exact rEnclosed_070
  · exact gapUpperCheck_070
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
