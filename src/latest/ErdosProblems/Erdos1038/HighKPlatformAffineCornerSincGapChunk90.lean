import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk90
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk90
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk90
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 90. -/

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

def sincGapLower_090 : Rat := 276999 / 1000000

theorem sincGap_090 : UniformLower (data ⟨90, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_090 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_090) (rOuter := rOuter_090)
      (gapUpper := gapUpper_090)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_090
  · exact rEnclosed_090
  · exact gapUpperCheck_090
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
