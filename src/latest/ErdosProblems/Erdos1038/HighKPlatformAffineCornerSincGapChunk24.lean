import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk24
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk24
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk24
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 24. -/

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

def sincGapLower_024 : Rat := 287999 / 1000000

theorem sincGap_024 : UniformLower (data ⟨24, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_024 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_024) (rOuter := rOuter_024)
      (gapUpper := gapUpper_024)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_024
  · exact rEnclosed_024
  · exact gapUpperCheck_024
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
