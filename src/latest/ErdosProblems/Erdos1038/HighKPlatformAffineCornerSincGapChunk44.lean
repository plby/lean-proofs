import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk44
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk44
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk44
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 44. -/

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

def sincGapLower_044 : Rat := 285999 / 1000000

theorem sincGap_044 : UniformLower (data ⟨44, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_044 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_044) (rOuter := rOuter_044)
      (gapUpper := gapUpper_044)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_044
  · exact rEnclosed_044
  · exact gapUpperCheck_044
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
