import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk116
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk116
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk116
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 116. -/

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

def sincGapLower_116 : Rat := 268999 / 1000000

theorem sincGap_116 : UniformLower (data ⟨116, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_116 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_116) (rOuter := rOuter_116)
      (gapUpper := gapUpper_116)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_116
  · exact rEnclosed_116
  · exact gapUpperCheck_116
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
