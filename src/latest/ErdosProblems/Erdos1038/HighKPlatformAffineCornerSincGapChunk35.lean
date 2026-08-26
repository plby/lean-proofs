import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk35
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk35
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk35
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 35. -/

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

def sincGapLower_035 : Rat := 286999 / 1000000

theorem sincGap_035 : UniformLower (data ⟨35, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_035 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_035) (rOuter := rOuter_035)
      (gapUpper := gapUpper_035)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_035
  · exact rEnclosed_035
  · exact gapUpperCheck_035
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
