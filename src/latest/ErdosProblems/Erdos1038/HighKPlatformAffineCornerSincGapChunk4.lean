import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk4
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk4
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk4
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 4. -/

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

def sincGapLower_004 : Rat := 287999 / 1000000

theorem sincGap_004 : UniformLower (data ⟨4, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_004 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_004) (rOuter := rOuter_004)
      (gapUpper := gapUpper_004)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_004
  · exact rEnclosed_004
  · exact gapUpperCheck_004
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
