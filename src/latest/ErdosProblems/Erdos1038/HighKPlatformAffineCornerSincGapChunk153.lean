import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk153
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk153
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk153
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 153. -/

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

def sincGapLower_153 : Rat := 254999 / 1000000

theorem sincGap_153 : UniformLower (data ⟨153, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_153 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_153) (rOuter := rOuter_153)
      (gapUpper := gapUpper_153)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_153
  · exact rEnclosed_153
  · exact gapUpperCheck_153
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
