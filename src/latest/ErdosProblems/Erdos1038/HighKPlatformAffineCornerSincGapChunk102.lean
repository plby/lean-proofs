import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk102
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk102
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk102
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 102. -/

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

def sincGapLower_102 : Rat := 272999 / 1000000

theorem sincGap_102 : UniformLower (data ⟨102, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_102 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_102) (rOuter := rOuter_102)
      (gapUpper := gapUpper_102)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_102
  · exact rEnclosed_102
  · exact gapUpperCheck_102
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
