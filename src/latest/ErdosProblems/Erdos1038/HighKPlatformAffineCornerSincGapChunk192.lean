import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk192
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk192
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk192
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 192. -/

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

def sincGapLower_192 : Rat := 237999 / 1000000

theorem sincGap_192 : UniformLower (data ⟨192, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_192 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_192) (rOuter := rOuter_192)
      (gapUpper := gapUpper_192)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_192
  · exact rEnclosed_192
  · exact gapUpperCheck_192
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
