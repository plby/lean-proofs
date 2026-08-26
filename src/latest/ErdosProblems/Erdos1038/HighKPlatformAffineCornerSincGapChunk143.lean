import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk143
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk143
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk143
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 143. -/

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

def sincGapLower_143 : Rat := 258999 / 1000000

theorem sincGap_143 : UniformLower (data ⟨143, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_143 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_143) (rOuter := rOuter_143)
      (gapUpper := gapUpper_143)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_143
  · exact rEnclosed_143
  · exact gapUpperCheck_143
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
