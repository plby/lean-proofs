import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk118
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk118
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk118
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 118. -/

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

def sincGapLower_118 : Rat := 267999 / 1000000

theorem sincGap_118 : UniformLower (data ⟨118, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_118 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_118) (rOuter := rOuter_118)
      (gapUpper := gapUpper_118)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_118
  · exact rEnclosed_118
  · exact gapUpperCheck_118
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
