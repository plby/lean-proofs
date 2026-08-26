import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk203
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk203
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk203
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 203. -/

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

def sincGapLower_203 : Rat := 232999 / 1000000

theorem sincGap_203 : UniformLower (data ⟨203, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_203 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_203) (rOuter := rOuter_203)
      (gapUpper := gapUpper_203)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_203
  · exact rEnclosed_203
  · exact gapUpperCheck_203
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
