import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk131
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk131
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk131
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 131. -/

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

def sincGapLower_131 : Rat := 263999 / 1000000

theorem sincGap_131 : UniformLower (data ⟨131, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_131 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_131) (rOuter := rOuter_131)
      (gapUpper := gapUpper_131)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_131
  · exact rEnclosed_131
  · exact gapUpperCheck_131
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
