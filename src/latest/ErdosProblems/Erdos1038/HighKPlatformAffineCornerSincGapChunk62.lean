import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk62
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk62
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk62
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 62. -/

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

def sincGapLower_062 : Rat := 282999 / 1000000

theorem sincGap_062 : UniformLower (data ⟨62, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_062 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_062) (rOuter := rOuter_062)
      (gapUpper := gapUpper_062)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_062
  · exact rEnclosed_062
  · exact gapUpperCheck_062
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
