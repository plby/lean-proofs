import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk69
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk69
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk69
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 69. -/

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

def sincGapLower_069 : Rat := 281999 / 1000000

theorem sincGap_069 : UniformLower (data ⟨69, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_069 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_069) (rOuter := rOuter_069)
      (gapUpper := gapUpper_069)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_069
  · exact rEnclosed_069
  · exact gapUpperCheck_069
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
