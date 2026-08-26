import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk57
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk57
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk57
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 57. -/

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

def sincGapLower_057 : Rat := 283999 / 1000000

theorem sincGap_057 : UniformLower (data ⟨57, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_057 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_057) (rOuter := rOuter_057)
      (gapUpper := gapUpper_057)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_057
  · exact rEnclosed_057
  · exact gapUpperCheck_057
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
