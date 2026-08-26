import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk78
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk78
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk78
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 78. -/

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

def sincGapLower_078 : Rat := 279999 / 1000000

theorem sincGap_078 : UniformLower (data ⟨78, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_078 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_078) (rOuter := rOuter_078)
      (gapUpper := gapUpper_078)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_078
  · exact rEnclosed_078
  · exact gapUpperCheck_078
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
