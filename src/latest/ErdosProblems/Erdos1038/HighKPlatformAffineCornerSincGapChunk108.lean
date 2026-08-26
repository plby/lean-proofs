import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk108
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk108
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk108
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 108. -/

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

def sincGapLower_108 : Rat := 271999 / 1000000

theorem sincGap_108 : UniformLower (data ⟨108, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_108 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_108) (rOuter := rOuter_108)
      (gapUpper := gapUpper_108)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_108
  · exact rEnclosed_108
  · exact gapUpperCheck_108
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
