import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk163
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk163
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk163
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 163. -/

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

def sincGapLower_163 : Rat := 250999 / 1000000

theorem sincGap_163 : UniformLower (data ⟨163, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_163 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_163) (rOuter := rOuter_163)
      (gapUpper := gapUpper_163)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_163
  · exact rEnclosed_163
  · exact gapUpperCheck_163
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
