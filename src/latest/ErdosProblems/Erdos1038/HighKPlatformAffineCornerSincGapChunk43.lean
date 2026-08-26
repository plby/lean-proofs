import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk43
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk43
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk43
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 43. -/

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

def sincGapLower_043 : Rat := 285999 / 1000000

theorem sincGap_043 : UniformLower (data ⟨43, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_043 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_043) (rOuter := rOuter_043)
      (gapUpper := gapUpper_043)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_043
  · exact rEnclosed_043
  · exact gapUpperCheck_043
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
