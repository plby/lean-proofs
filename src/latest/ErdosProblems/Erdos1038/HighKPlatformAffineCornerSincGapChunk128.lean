import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk128
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk128
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk128
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 128. -/

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

def sincGapLower_128 : Rat := 264999 / 1000000

theorem sincGap_128 : UniformLower (data ⟨128, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_128 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_128) (rOuter := rOuter_128)
      (gapUpper := gapUpper_128)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_128
  · exact rEnclosed_128
  · exact gapUpperCheck_128
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
