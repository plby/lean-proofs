import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk216
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk216
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk216
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 216. -/

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

def sincGapLower_216 : Rat := 225999 / 1000000

theorem sincGap_216 : UniformLower (data ⟨216, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_216 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_216) (rOuter := rOuter_216)
      (gapUpper := gapUpper_216)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_216
  · exact rEnclosed_216
  · exact gapUpperCheck_216
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
