import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk250
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk250
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk250
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 250. -/

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

def sincGapLower_250 : Rat := 208999 / 1000000

theorem sincGap_250 : UniformLower (data ⟨250, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_250 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_250) (rOuter := rOuter_250)
      (gapUpper := gapUpper_250)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_250
  · exact rEnclosed_250
  · exact gapUpperCheck_250
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
