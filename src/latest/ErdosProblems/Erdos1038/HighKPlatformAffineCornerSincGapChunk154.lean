import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk154
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk154
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk154
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 154. -/

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

def sincGapLower_154 : Rat := 254999 / 1000000

theorem sincGap_154 : UniformLower (data ⟨154, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_154 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_154) (rOuter := rOuter_154)
      (gapUpper := gapUpper_154)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_154
  · exact rEnclosed_154
  · exact gapUpperCheck_154
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
