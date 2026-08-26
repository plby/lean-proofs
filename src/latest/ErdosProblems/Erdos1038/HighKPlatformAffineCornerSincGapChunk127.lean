import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk127
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk127
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk127
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 127. -/

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

def sincGapLower_127 : Rat := 264999 / 1000000

theorem sincGap_127 : UniformLower (data ⟨127, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_127 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_127) (rOuter := rOuter_127)
      (gapUpper := gapUpper_127)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_127
  · exact rEnclosed_127
  · exact gapUpperCheck_127
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
