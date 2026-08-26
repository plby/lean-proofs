import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk242
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk242
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk242
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 242. -/

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

def sincGapLower_242 : Rat := 212999 / 1000000

theorem sincGap_242 : UniformLower (data ⟨242, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_242 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_242) (rOuter := rOuter_242)
      (gapUpper := gapUpper_242)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_242
  · exact rEnclosed_242
  · exact gapUpperCheck_242
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
