import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk240
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk240
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk240
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 240. -/

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

def sincGapLower_240 : Rat := 213999 / 1000000

theorem sincGap_240 : UniformLower (data ⟨240, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_240 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_240) (rOuter := rOuter_240)
      (gapUpper := gapUpper_240)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_240
  · exact rEnclosed_240
  · exact gapUpperCheck_240
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
