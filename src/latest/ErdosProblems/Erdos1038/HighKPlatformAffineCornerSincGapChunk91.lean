import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk91
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk91
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk91
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 91. -/

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

def sincGapLower_091 : Rat := 276999 / 1000000

theorem sincGap_091 : UniformLower (data ⟨91, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_091 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_091) (rOuter := rOuter_091)
      (gapUpper := gapUpper_091)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_091
  · exact rEnclosed_091
  · exact gapUpperCheck_091
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
