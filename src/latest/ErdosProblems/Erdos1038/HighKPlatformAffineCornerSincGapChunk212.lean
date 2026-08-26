import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk212
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk212
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk212
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 212. -/

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

def sincGapLower_212 : Rat := 227999 / 1000000

theorem sincGap_212 : UniformLower (data ⟨212, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_212 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_212) (rOuter := rOuter_212)
      (gapUpper := gapUpper_212)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_212
  · exact rEnclosed_212
  · exact gapUpperCheck_212
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
