import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk28
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk28
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk28
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 28. -/

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

def sincGapLower_028 : Rat := 286999 / 1000000

theorem sincGap_028 : UniformLower (data ⟨28, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_028 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_028) (rOuter := rOuter_028)
      (gapUpper := gapUpper_028)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_028
  · exact rEnclosed_028
  · exact gapUpperCheck_028
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
