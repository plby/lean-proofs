import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk74
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk74
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk74
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 74. -/

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

def sincGapLower_074 : Rat := 280999 / 1000000

theorem sincGap_074 : UniformLower (data ⟨74, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_074 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_074) (rOuter := rOuter_074)
      (gapUpper := gapUpper_074)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_074
  · exact rEnclosed_074
  · exact gapUpperCheck_074
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
