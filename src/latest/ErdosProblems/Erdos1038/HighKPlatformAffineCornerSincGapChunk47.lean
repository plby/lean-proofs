import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk47
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk47
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk47
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 47. -/

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

def sincGapLower_047 : Rat := 285999 / 1000000

theorem sincGap_047 : UniformLower (data ⟨47, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_047 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_047) (rOuter := rOuter_047)
      (gapUpper := gapUpper_047)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_047
  · exact rEnclosed_047
  · exact gapUpperCheck_047
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
