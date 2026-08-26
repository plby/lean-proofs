import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk68
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk68
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk68
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 68. -/

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

def sincGapLower_068 : Rat := 281999 / 1000000

theorem sincGap_068 : UniformLower (data ⟨68, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_068 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_068) (rOuter := rOuter_068)
      (gapUpper := gapUpper_068)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_068
  · exact rEnclosed_068
  · exact gapUpperCheck_068
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
