import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk160
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk160
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk160
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 160. -/

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

def sincGapLower_160 : Rat := 251999 / 1000000

theorem sincGap_160 : UniformLower (data ⟨160, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_160 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_160) (rOuter := rOuter_160)
      (gapUpper := gapUpper_160)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_160
  · exact rEnclosed_160
  · exact gapUpperCheck_160
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
