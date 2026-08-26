import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk173
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk173
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk173
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 173. -/

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

def sincGapLower_173 : Rat := 245999 / 1000000

theorem sincGap_173 : UniformLower (data ⟨173, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_173 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_173) (rOuter := rOuter_173)
      (gapUpper := gapUpper_173)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_173
  · exact rEnclosed_173
  · exact gapUpperCheck_173
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
