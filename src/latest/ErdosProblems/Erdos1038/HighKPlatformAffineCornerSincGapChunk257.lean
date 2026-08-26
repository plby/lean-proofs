import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk257
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk257
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk257
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 257. -/

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

def sincGapLower_257 : Rat := 205999 / 1000000

theorem sincGap_257 : UniformLower (data ⟨257, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_257 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_257) (rOuter := rOuter_257)
      (gapUpper := gapUpper_257)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_257
  · exact rEnclosed_257
  · exact gapUpperCheck_257
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
