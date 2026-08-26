import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk119
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk119
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk119
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 119. -/

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

def sincGapLower_119 : Rat := 267999 / 1000000

theorem sincGap_119 : UniformLower (data ⟨119, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_119 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_119) (rOuter := rOuter_119)
      (gapUpper := gapUpper_119)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_119
  · exact rEnclosed_119
  · exact gapUpperCheck_119
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
