import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk138
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk138
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk138
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 138. -/

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

def sincGapLower_138 : Rat := 260999 / 1000000

theorem sincGap_138 : UniformLower (data ⟨138, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_138 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_138) (rOuter := rOuter_138)
      (gapUpper := gapUpper_138)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_138
  · exact rEnclosed_138
  · exact gapUpperCheck_138
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
