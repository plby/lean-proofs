import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk65
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk65
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk65
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 65. -/

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

def sincGapLower_065 : Rat := 282999 / 1000000

theorem sincGap_065 : UniformLower (data ⟨65, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_065 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_065) (rOuter := rOuter_065)
      (gapUpper := gapUpper_065)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_065
  · exact rEnclosed_065
  · exact gapUpperCheck_065
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
