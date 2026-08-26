import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk256
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk256
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk256
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 256. -/

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

def sincGapLower_256 : Rat := 205999 / 1000000

theorem sincGap_256 : UniformLower (data ⟨256, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_256 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_256) (rOuter := rOuter_256)
      (gapUpper := gapUpper_256)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_256
  · exact rEnclosed_256
  · exact gapUpperCheck_256
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
