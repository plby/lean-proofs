import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk147
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk147
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk147
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 147. -/

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

def sincGapLower_147 : Rat := 256999 / 1000000

theorem sincGap_147 : UniformLower (data ⟨147, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_147 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_147) (rOuter := rOuter_147)
      (gapUpper := gapUpper_147)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_147
  · exact rEnclosed_147
  · exact gapUpperCheck_147
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
