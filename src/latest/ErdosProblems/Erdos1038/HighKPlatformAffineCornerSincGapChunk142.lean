import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk142
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk142
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk142
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 142. -/

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

def sincGapLower_142 : Rat := 258999 / 1000000

theorem sincGap_142 : UniformLower (data ⟨142, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_142 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_142) (rOuter := rOuter_142)
      (gapUpper := gapUpper_142)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_142
  · exact rEnclosed_142
  · exact gapUpperCheck_142
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
