import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk52
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk52
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk52
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 52. -/

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

def sincGapLower_052 : Rat := 284999 / 1000000

theorem sincGap_052 : UniformLower (data ⟨52, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_052 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_052) (rOuter := rOuter_052)
      (gapUpper := gapUpper_052)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_052
  · exact rEnclosed_052
  · exact gapUpperCheck_052
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
