import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk243
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk243
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk243
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 243. -/

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

def sincGapLower_243 : Rat := 212999 / 1000000

theorem sincGap_243 : UniformLower (data ⟨243, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_243 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_243) (rOuter := rOuter_243)
      (gapUpper := gapUpper_243)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_243
  · exact rEnclosed_243
  · exact gapUpperCheck_243
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
