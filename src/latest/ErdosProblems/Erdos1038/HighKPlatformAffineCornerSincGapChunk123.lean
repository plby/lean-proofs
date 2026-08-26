import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk123
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk123
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk123
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 123. -/

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

def sincGapLower_123 : Rat := 266999 / 1000000

theorem sincGap_123 : UniformLower (data ⟨123, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_123 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_123) (rOuter := rOuter_123)
      (gapUpper := gapUpper_123)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_123
  · exact rEnclosed_123
  · exact gapUpperCheck_123
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
