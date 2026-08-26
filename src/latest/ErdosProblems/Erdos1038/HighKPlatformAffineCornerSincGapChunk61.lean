import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk61
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk61
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk61
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 61. -/

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

def sincGapLower_061 : Rat := 282999 / 1000000

theorem sincGap_061 : UniformLower (data ⟨61, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_061 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_061) (rOuter := rOuter_061)
      (gapUpper := gapUpper_061)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_061
  · exact rEnclosed_061
  · exact gapUpperCheck_061
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
