import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk2
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk2
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk2
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 2. -/

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

def sincGapLower_002 : Rat := 287999 / 1000000

theorem sincGap_002 : UniformLower (data ⟨2, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_002 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_002) (rOuter := rOuter_002)
      (gapUpper := gapUpper_002)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_002
  · exact rEnclosed_002
  · exact gapUpperCheck_002
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
