import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk137
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk137
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk137
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 137. -/

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

def sincGapLower_137 : Rat := 260999 / 1000000

theorem sincGap_137 : UniformLower (data ⟨137, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_137 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_137) (rOuter := rOuter_137)
      (gapUpper := gapUpper_137)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_137
  · exact rEnclosed_137
  · exact gapUpperCheck_137
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
