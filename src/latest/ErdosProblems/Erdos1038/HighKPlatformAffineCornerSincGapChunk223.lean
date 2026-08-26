import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk223
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk223
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk223
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 223. -/

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

def sincGapLower_223 : Rat := 222999 / 1000000

theorem sincGap_223 : UniformLower (data ⟨223, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_223 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_223) (rOuter := rOuter_223)
      (gapUpper := gapUpper_223)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_223
  · exact rEnclosed_223
  · exact gapUpperCheck_223
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
