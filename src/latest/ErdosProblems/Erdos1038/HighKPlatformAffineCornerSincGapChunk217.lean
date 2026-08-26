import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk217
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk217
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk217
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 217. -/

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

def sincGapLower_217 : Rat := 225999 / 1000000

theorem sincGap_217 : UniformLower (data ⟨217, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_217 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_217) (rOuter := rOuter_217)
      (gapUpper := gapUpper_217)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_217
  · exact rEnclosed_217
  · exact gapUpperCheck_217
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
