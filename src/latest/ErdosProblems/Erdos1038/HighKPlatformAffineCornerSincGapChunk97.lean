import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk97
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk97
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk97
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 97. -/

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

def sincGapLower_097 : Rat := 274999 / 1000000

theorem sincGap_097 : UniformLower (data ⟨97, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_097 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_097) (rOuter := rOuter_097)
      (gapUpper := gapUpper_097)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_097
  · exact rEnclosed_097
  · exact gapUpperCheck_097
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
