import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk54
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk54
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk54
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 54. -/

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

def sincGapLower_054 : Rat := 284999 / 1000000

theorem sincGap_054 : UniformLower (data ⟨54, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_054 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_054) (rOuter := rOuter_054)
      (gapUpper := gapUpper_054)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_054
  · exact rEnclosed_054
  · exact gapUpperCheck_054
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
