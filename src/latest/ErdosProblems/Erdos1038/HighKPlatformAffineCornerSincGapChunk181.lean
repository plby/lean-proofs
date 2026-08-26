import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk181
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk181
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk181
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 181. -/

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

def sincGapLower_181 : Rat := 242999 / 1000000

theorem sincGap_181 : UniformLower (data ⟨181, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_181 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_181) (rOuter := rOuter_181)
      (gapUpper := gapUpper_181)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_181
  · exact rEnclosed_181
  · exact gapUpperCheck_181
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
