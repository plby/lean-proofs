import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk124
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk124
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk124
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 124. -/

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

def sincGapLower_124 : Rat := 265999 / 1000000

theorem sincGap_124 : UniformLower (data ⟨124, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_124 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_124) (rOuter := rOuter_124)
      (gapUpper := gapUpper_124)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_124
  · exact rEnclosed_124
  · exact gapUpperCheck_124
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
