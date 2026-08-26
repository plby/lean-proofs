import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk115
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk115
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk115
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 115. -/

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

def sincGapLower_115 : Rat := 268999 / 1000000

theorem sincGap_115 : UniformLower (data ⟨115, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_115 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_115) (rOuter := rOuter_115)
      (gapUpper := gapUpper_115)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_115
  · exact rEnclosed_115
  · exact gapUpperCheck_115
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
