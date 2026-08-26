import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk174
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk174
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk174
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 174. -/

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

def sincGapLower_174 : Rat := 245999 / 1000000

theorem sincGap_174 : UniformLower (data ⟨174, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_174 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_174) (rOuter := rOuter_174)
      (gapUpper := gapUpper_174)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_174
  · exact rEnclosed_174
  · exact gapUpperCheck_174
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
