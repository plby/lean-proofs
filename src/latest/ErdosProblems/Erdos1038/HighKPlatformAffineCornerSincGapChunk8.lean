import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk8
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk8
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk8
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 8. -/

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

def sincGapLower_008 : Rat := 287999 / 1000000

theorem sincGap_008 : UniformLower (data ⟨8, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_008 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_008) (rOuter := rOuter_008)
      (gapUpper := gapUpper_008)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_008
  · exact rEnclosed_008
  · exact gapUpperCheck_008
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
