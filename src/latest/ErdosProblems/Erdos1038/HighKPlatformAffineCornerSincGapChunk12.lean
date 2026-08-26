import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk12
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk12
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk12
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 12. -/

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

def sincGapLower_012 : Rat := 287999 / 1000000

theorem sincGap_012 : UniformLower (data ⟨12, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_012 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_012) (rOuter := rOuter_012)
      (gapUpper := gapUpper_012)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_012
  · exact rEnclosed_012
  · exact gapUpperCheck_012
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
