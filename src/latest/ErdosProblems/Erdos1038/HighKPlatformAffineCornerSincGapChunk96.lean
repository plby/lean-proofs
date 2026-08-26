import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk96
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk96
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk96
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 96. -/

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

def sincGapLower_096 : Rat := 274999 / 1000000

theorem sincGap_096 : UniformLower (data ⟨96, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_096 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_096) (rOuter := rOuter_096)
      (gapUpper := gapUpper_096)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_096
  · exact rEnclosed_096
  · exact gapUpperCheck_096
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
