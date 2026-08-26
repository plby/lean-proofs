import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk95
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk95
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk95
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 95. -/

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

def sincGapLower_095 : Rat := 274999 / 1000000

theorem sincGap_095 : UniformLower (data ⟨95, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_095 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_095) (rOuter := rOuter_095)
      (gapUpper := gapUpper_095)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_095
  · exact rEnclosed_095
  · exact gapUpperCheck_095
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
