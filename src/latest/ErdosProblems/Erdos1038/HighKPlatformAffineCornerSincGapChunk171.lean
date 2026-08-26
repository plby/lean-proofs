import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk171
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk171
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk171
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 171. -/

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

def sincGapLower_171 : Rat := 246999 / 1000000

theorem sincGap_171 : UniformLower (data ⟨171, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_171 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_171) (rOuter := rOuter_171)
      (gapUpper := gapUpper_171)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_171
  · exact rEnclosed_171
  · exact gapUpperCheck_171
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
