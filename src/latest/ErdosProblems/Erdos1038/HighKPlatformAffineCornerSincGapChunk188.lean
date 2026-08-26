import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk188
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk188
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk188
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 188. -/

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

def sincGapLower_188 : Rat := 239999 / 1000000

theorem sincGap_188 : UniformLower (data ⟨188, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_188 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_188) (rOuter := rOuter_188)
      (gapUpper := gapUpper_188)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_188
  · exact rEnclosed_188
  · exact gapUpperCheck_188
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
