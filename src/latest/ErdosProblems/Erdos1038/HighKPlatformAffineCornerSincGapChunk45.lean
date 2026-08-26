import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk45
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk45
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk45
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 45. -/

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

def sincGapLower_045 : Rat := 285999 / 1000000

theorem sincGap_045 : UniformLower (data ⟨45, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_045 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_045) (rOuter := rOuter_045)
      (gapUpper := gapUpper_045)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_045
  · exact rEnclosed_045
  · exact gapUpperCheck_045
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
