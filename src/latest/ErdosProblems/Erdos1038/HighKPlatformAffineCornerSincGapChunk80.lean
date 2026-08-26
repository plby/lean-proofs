import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk80
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk80
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk80
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 80. -/

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

def sincGapLower_080 : Rat := 278999 / 1000000

theorem sincGap_080 : UniformLower (data ⟨80, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_080 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_080) (rOuter := rOuter_080)
      (gapUpper := gapUpper_080)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_080
  · exact rEnclosed_080
  · exact gapUpperCheck_080
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
