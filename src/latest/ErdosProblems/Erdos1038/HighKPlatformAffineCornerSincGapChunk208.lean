import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk208
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk208
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk208
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 208. -/

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

def sincGapLower_208 : Rat := 229999 / 1000000

theorem sincGap_208 : UniformLower (data ⟨208, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_208 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_208) (rOuter := rOuter_208)
      (gapUpper := gapUpper_208)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_208
  · exact rEnclosed_208
  · exact gapUpperCheck_208
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
