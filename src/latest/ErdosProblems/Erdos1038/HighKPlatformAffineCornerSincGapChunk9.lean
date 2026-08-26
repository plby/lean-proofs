import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk9
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk9
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk9
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 9. -/

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

def sincGapLower_009 : Rat := 287999 / 1000000

theorem sincGap_009 : UniformLower (data ⟨9, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_009 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_009) (rOuter := rOuter_009)
      (gapUpper := gapUpper_009)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_009
  · exact rEnclosed_009
  · exact gapUpperCheck_009
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
