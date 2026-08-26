import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk222
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk222
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk222
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 222. -/

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

def sincGapLower_222 : Rat := 222999 / 1000000

theorem sincGap_222 : UniformLower (data ⟨222, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_222 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_222) (rOuter := rOuter_222)
      (gapUpper := gapUpper_222)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_222
  · exact rEnclosed_222
  · exact gapUpperCheck_222
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
