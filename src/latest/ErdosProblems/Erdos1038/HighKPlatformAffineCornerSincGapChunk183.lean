import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk183
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk183
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk183
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 183. -/

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

def sincGapLower_183 : Rat := 241999 / 1000000

theorem sincGap_183 : UniformLower (data ⟨183, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_183 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_183) (rOuter := rOuter_183)
      (gapUpper := gapUpper_183)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_183
  · exact rEnclosed_183
  · exact gapUpperCheck_183
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
