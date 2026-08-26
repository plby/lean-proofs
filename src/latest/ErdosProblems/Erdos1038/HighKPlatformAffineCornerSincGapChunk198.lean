import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk198
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk198
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk198
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 198. -/

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

def sincGapLower_198 : Rat := 234999 / 1000000

theorem sincGap_198 : UniformLower (data ⟨198, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_198 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_198) (rOuter := rOuter_198)
      (gapUpper := gapUpper_198)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_198
  · exact rEnclosed_198
  · exact gapUpperCheck_198
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
