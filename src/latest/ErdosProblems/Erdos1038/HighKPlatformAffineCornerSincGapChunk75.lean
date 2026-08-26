import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk75
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk75
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk75
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 75. -/

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

def sincGapLower_075 : Rat := 280999 / 1000000

theorem sincGap_075 : UniformLower (data ⟨75, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_075 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_075) (rOuter := rOuter_075)
      (gapUpper := gapUpper_075)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_075
  · exact rEnclosed_075
  · exact gapUpperCheck_075
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
