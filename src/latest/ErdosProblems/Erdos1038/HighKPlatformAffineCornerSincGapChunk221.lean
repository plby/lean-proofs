import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk221
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk221
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk221
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 221. -/

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

def sincGapLower_221 : Rat := 223999 / 1000000

theorem sincGap_221 : UniformLower (data ⟨221, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_221 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_221) (rOuter := rOuter_221)
      (gapUpper := gapUpper_221)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_221
  · exact rEnclosed_221
  · exact gapUpperCheck_221
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
