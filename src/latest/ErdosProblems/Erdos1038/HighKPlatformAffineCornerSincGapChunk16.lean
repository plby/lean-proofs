import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk16
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk16
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk16
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 16. -/

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

def sincGapLower_016 : Rat := 287999 / 1000000

theorem sincGap_016 : UniformLower (data ⟨16, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_016 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_016) (rOuter := rOuter_016)
      (gapUpper := gapUpper_016)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_016
  · exact rEnclosed_016
  · exact gapUpperCheck_016
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
