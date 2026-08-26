import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk121
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk121
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk121
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 121. -/

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

def sincGapLower_121 : Rat := 266999 / 1000000

theorem sincGap_121 : UniformLower (data ⟨121, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_121 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_121) (rOuter := rOuter_121)
      (gapUpper := gapUpper_121)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_121
  · exact rEnclosed_121
  · exact gapUpperCheck_121
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
