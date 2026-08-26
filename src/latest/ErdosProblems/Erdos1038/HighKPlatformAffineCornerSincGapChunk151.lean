import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk151
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk151
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk151
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 151. -/

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

def sincGapLower_151 : Rat := 255999 / 1000000

theorem sincGap_151 : UniformLower (data ⟨151, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_151 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_151) (rOuter := rOuter_151)
      (gapUpper := gapUpper_151)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_151
  · exact rEnclosed_151
  · exact gapUpperCheck_151
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
