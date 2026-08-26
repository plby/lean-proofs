import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk133
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk133
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk133
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 133. -/

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

def sincGapLower_133 : Rat := 262999 / 1000000

theorem sincGap_133 : UniformLower (data ⟨133, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_133 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_133) (rOuter := rOuter_133)
      (gapUpper := gapUpper_133)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_133
  · exact rEnclosed_133
  · exact gapUpperCheck_133
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
