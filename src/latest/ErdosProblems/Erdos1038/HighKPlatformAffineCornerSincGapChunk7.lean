import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk7
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk7
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk7
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 7. -/

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

def sincGapLower_007 : Rat := 287999 / 1000000

theorem sincGap_007 : UniformLower (data ⟨7, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_007 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_007) (rOuter := rOuter_007)
      (gapUpper := gapUpper_007)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_007
  · exact rEnclosed_007
  · exact gapUpperCheck_007
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
