import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk3
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk3
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk3
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 3. -/

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

def sincGapLower_003 : Rat := 287999 / 1000000

theorem sincGap_003 : UniformLower (data ⟨3, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_003 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_003) (rOuter := rOuter_003)
      (gapUpper := gapUpper_003)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_003
  · exact rEnclosed_003
  · exact gapUpperCheck_003
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
