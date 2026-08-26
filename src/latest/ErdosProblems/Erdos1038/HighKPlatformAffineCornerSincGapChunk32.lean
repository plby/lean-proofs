import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk32
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk32
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk32
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 32. -/

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

def sincGapLower_032 : Rat := 286999 / 1000000

theorem sincGap_032 : UniformLower (data ⟨32, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_032 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_032) (rOuter := rOuter_032)
      (gapUpper := gapUpper_032)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_032
  · exact rEnclosed_032
  · exact gapUpperCheck_032
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
