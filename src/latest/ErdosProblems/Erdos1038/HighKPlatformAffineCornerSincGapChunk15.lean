import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk15
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk15
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk15
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 15. -/

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

def sincGapLower_015 : Rat := 287999 / 1000000

theorem sincGap_015 : UniformLower (data ⟨15, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_015 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_015) (rOuter := rOuter_015)
      (gapUpper := gapUpper_015)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_015
  · exact rEnclosed_015
  · exact gapUpperCheck_015
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
