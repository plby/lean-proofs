import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk229
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk229
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk229
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 229. -/

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

def sincGapLower_229 : Rat := 219999 / 1000000

theorem sincGap_229 : UniformLower (data ⟨229, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_229 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_229) (rOuter := rOuter_229)
      (gapUpper := gapUpper_229)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_229
  · exact rEnclosed_229
  · exact gapUpperCheck_229
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
