import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk120
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk120
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk120
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 120. -/

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

def sincGapLower_120 : Rat := 267999 / 1000000

theorem sincGap_120 : UniformLower (data ⟨120, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_120 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_120) (rOuter := rOuter_120)
      (gapUpper := gapUpper_120)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_120
  · exact rEnclosed_120
  · exact gapUpperCheck_120
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
