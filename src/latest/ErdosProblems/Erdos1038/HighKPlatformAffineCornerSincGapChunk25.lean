import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk25
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk25
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk25
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 25. -/

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

def sincGapLower_025 : Rat := 287999 / 1000000

theorem sincGap_025 : UniformLower (data ⟨25, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_025 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_025) (rOuter := rOuter_025)
      (gapUpper := gapUpper_025)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_025
  · exact rEnclosed_025
  · exact gapUpperCheck_025
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
