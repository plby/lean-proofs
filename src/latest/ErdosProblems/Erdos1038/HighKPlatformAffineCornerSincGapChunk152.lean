import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk152
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk152
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk152
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 152. -/

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

def sincGapLower_152 : Rat := 254999 / 1000000

theorem sincGap_152 : UniformLower (data ⟨152, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_152 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_152) (rOuter := rOuter_152)
      (gapUpper := gapUpper_152)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_152
  · exact rEnclosed_152
  · exact gapUpperCheck_152
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
