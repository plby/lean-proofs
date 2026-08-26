import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk209
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk209
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk209
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 209. -/

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

def sincGapLower_209 : Rat := 229999 / 1000000

theorem sincGap_209 : UniformLower (data ⟨209, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_209 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_209) (rOuter := rOuter_209)
      (gapUpper := gapUpper_209)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_209
  · exact rEnclosed_209
  · exact gapUpperCheck_209
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
