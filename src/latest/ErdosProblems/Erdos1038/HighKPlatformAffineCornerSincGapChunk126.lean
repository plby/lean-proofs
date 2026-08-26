import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk126
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk126
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk126
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 126. -/

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

def sincGapLower_126 : Rat := 264999 / 1000000

theorem sincGap_126 : UniformLower (data ⟨126, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_126 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_126) (rOuter := rOuter_126)
      (gapUpper := gapUpper_126)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_126
  · exact rEnclosed_126
  · exact gapUpperCheck_126
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
