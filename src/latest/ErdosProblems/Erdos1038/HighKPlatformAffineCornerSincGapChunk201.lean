import ErdosProblems.Erdos1038.HighKPlatformAffineCornerQEnclosureChunk201
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerREnclosureChunk201
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk201
import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineSemanticCorner
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 201. -/

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

def sincGapLower_201 : Rat := 233999 / 1000000

theorem sincGap_201 : UniformLower (data ⟨201, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_201 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_201) (rOuter := rOuter_201)
      (gapUpper := gapUpper_201)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_201
  · exact rEnclosed_201
  · exact gapUpperCheck_201
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
