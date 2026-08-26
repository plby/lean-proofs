import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk202
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk202
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk202
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 202. -/

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

def sincGapLower_202 : Rat := 232999 / 1000000

theorem sincGap_202 : UniformLower (data ⟨202, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_202 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_202) (rOuter := rOuter_202)
      (gapUpper := gapUpper_202)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_202
  · exact rEnclosed_202
  · exact gapUpperCheck_202
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
