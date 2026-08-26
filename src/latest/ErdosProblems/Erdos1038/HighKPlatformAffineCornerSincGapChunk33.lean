import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk33
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk33
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk33
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 33. -/

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

def sincGapLower_033 : Rat := 286999 / 1000000

theorem sincGap_033 : UniformLower (data ⟨33, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_033 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_033) (rOuter := rOuter_033)
      (gapUpper := gapUpper_033)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_033
  · exact rEnclosed_033
  · exact gapUpperCheck_033
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
