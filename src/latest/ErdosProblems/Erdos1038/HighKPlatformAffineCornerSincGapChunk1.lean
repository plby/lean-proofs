import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk1
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk1
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk1
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 1. -/

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

def sincGapLower_001 : Rat := 287999 / 1000000

theorem sincGap_001 : UniformLower (data ⟨1, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_001 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_001) (rOuter := rOuter_001)
      (gapUpper := gapUpper_001)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_001
  · exact rEnclosed_001
  · exact gapUpperCheck_001
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
