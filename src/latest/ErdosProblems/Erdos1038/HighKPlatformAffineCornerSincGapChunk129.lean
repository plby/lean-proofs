import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk129
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk129
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk129
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 129. -/

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

def sincGapLower_129 : Rat := 263999 / 1000000

theorem sincGap_129 : UniformLower (data ⟨129, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_129 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_129) (rOuter := rOuter_129)
      (gapUpper := gapUpper_129)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_129
  · exact rEnclosed_129
  · exact gapUpperCheck_129
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
