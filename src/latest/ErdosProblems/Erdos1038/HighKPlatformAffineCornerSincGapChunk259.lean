import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk259
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk259
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk259
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 259. -/

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

def sincGapLower_259 : Rat := 204999 / 1000000

theorem sincGap_259 : UniformLower (data ⟨259, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_259 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_259) (rOuter := rOuter_259)
      (gapUpper := gapUpper_259)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_259
  · exact rEnclosed_259
  · exact gapUpperCheck_259
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
