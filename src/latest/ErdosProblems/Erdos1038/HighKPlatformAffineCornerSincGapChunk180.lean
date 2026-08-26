import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk180
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk180
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk180
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 180. -/

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

def sincGapLower_180 : Rat := 242999 / 1000000

theorem sincGap_180 : UniformLower (data ⟨180, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_180 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_180) (rOuter := rOuter_180)
      (gapUpper := gapUpper_180)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_180
  · exact rEnclosed_180
  · exact gapUpperCheck_180
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
