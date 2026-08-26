import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk100
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk100
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk100
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 100. -/

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

def sincGapLower_100 : Rat := 273999 / 1000000

theorem sincGap_100 : UniformLower (data ⟨100, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_100 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_100) (rOuter := rOuter_100)
      (gapUpper := gapUpper_100)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_100
  · exact rEnclosed_100
  · exact gapUpperCheck_100
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
