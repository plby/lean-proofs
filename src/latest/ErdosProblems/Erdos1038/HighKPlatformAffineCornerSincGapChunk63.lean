import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk63
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk63
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk63
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 63. -/

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

def sincGapLower_063 : Rat := 282999 / 1000000

theorem sincGap_063 : UniformLower (data ⟨63, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_063 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_063) (rOuter := rOuter_063)
      (gapUpper := gapUpper_063)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_063
  · exact rEnclosed_063
  · exact gapUpperCheck_063
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
