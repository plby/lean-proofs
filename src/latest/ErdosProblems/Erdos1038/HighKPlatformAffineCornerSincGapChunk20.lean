import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk20
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk20
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk20
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 20. -/

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

def sincGapLower_020 : Rat := 287999 / 1000000

theorem sincGap_020 : UniformLower (data ⟨20, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_020 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_020) (rOuter := rOuter_020)
      (gapUpper := gapUpper_020)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_020
  · exact rEnclosed_020
  · exact gapUpperCheck_020
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
