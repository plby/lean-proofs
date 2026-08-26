import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk157
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk157
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk157
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 157. -/

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

def sincGapLower_157 : Rat := 252999 / 1000000

theorem sincGap_157 : UniformLower (data ⟨157, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_157 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_157) (rOuter := rOuter_157)
      (gapUpper := gapUpper_157)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_157
  · exact rEnclosed_157
  · exact gapUpperCheck_157
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
