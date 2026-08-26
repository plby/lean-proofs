import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk27
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk27
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk27
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 27. -/

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

def sincGapLower_027 : Rat := 287999 / 1000000

theorem sincGap_027 : UniformLower (data ⟨27, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_027 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_027) (rOuter := rOuter_027)
      (gapUpper := gapUpper_027)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_027
  · exact rEnclosed_027
  · exact gapUpperCheck_027
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
