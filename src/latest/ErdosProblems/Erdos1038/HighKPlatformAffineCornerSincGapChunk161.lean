import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk161
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk161
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk161
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 161. -/

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

def sincGapLower_161 : Rat := 251999 / 1000000

theorem sincGap_161 : UniformLower (data ⟨161, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_161 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_161) (rOuter := rOuter_161)
      (gapUpper := gapUpper_161)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_161
  · exact rEnclosed_161
  · exact gapUpperCheck_161
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
