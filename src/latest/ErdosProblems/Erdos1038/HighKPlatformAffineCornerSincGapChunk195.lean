import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk195
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk195
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk195
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 195. -/

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

def sincGapLower_195 : Rat := 235999 / 1000000

theorem sincGap_195 : UniformLower (data ⟨195, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_195 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_195) (rOuter := rOuter_195)
      (gapUpper := gapUpper_195)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_195
  · exact rEnclosed_195
  · exact gapUpperCheck_195
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
