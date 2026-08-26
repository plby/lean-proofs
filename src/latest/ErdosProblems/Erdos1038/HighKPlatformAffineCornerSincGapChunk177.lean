import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk177
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk177
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk177
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 177. -/

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

def sincGapLower_177 : Rat := 244999 / 1000000

theorem sincGap_177 : UniformLower (data ⟨177, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_177 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_177) (rOuter := rOuter_177)
      (gapUpper := gapUpper_177)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_177
  · exact rEnclosed_177
  · exact gapUpperCheck_177
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
