import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk230
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk230
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk230
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 230. -/

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

def sincGapLower_230 : Rat := 219999 / 1000000

theorem sincGap_230 : UniformLower (data ⟨230, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_230 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_230) (rOuter := rOuter_230)
      (gapUpper := gapUpper_230)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_230
  · exact rEnclosed_230
  · exact gapUpperCheck_230
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
