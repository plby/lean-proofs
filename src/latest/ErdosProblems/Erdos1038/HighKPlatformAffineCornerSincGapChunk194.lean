import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk194
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk194
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk194
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 194. -/

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

def sincGapLower_194 : Rat := 236999 / 1000000

theorem sincGap_194 : UniformLower (data ⟨194, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_194 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_194) (rOuter := rOuter_194)
      (gapUpper := gapUpper_194)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_194
  · exact rEnclosed_194
  · exact gapUpperCheck_194
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
