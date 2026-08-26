import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineCorrectionCertificateCap169
import ErdosProblems.Erdos1038.HighKPlatformAffineCorrectionCertificateCap294
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerPrefactorChunk169
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerPenaltyChunk169
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapChunk169
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated proof-producing checks for affine-table cells. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineTableChunk169

open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineTableData
open Erdos1038 HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCornerComponents
open Erdos1038.HighKPlatformAffineSemanticCorner
open Erdos1038.HighKPlatformAffineCornerLeafCertificates
open Erdos1038.HighKPlatformAffineCorrectionCertificates

theorem raw_169 : RawChecks (data ⟨169, by decide⟩) := by
  apply (rawChecks_iff_tuple _).2
  unfold RawCheckTuple
  -- k_lt
  constructor
  · kernel_decide
  -- xm_lt
  constructor
  · kernel_decide
  -- xp_lt
  constructor
  · kernel_decide
  -- xm_negative
  constructor
  · kernel_decide
  -- xp_positive
  constructor
  · kernel_decide
  -- edge_hi_positive
  constructor
  · kernel_decide
  -- xm_lt_edge_hi
  constructor
  · kernel_decide
  -- xp_lt_edge_hi
  constructor
  · kernel_decide
  -- edge_lo_lt_two
  constructor
  · kernel_decide
  -- global_k_lo
  constructor
  · kernel_decide
  -- global_k_hi
  constructor
  · kernel_decide
  -- global_xm_lo
  constructor
  · kernel_decide
  -- global_xm_hi
  constructor
  · kernel_decide
  -- global_xp_lo
  constructor
  · kernel_decide
  -- global_xp_hi
  constructor
  · kernel_decide
  -- minusAtLoLeft
  constructor
  · kernel_decide
  -- minusAtLoRight
  constructor
  · kernel_decide
  -- minusAtHiLeft
  constructor
  · kernel_decide
  -- minusAtHiRight
  constructor
  · kernel_decide
  -- plusAtLoLeft
  constructor
  · kernel_decide
  -- plusAtLoRight
  constructor
  · kernel_decide
  -- plusAtHiLeft
  constructor
  · kernel_decide
  -- plusAtHiRight
  constructor
  · kernel_decide
  -- minusWx
  constructor
  · kernel_decide
  -- plusWx
  constructor
  · kernel_decide
  -- minusSlope_eval
  constructor
  · kernel_decide
  -- plusSlope_eval
  constructor
  · kernel_decide
  -- minusSlope_ordered
  constructor
  · kernel_decide
  -- plusSlope_ordered
  constructor
  · kernel_decide
  -- minusSlope_negative
  constructor
  · kernel_decide
  -- plusSlope_positive
  constructor
  · kernel_decide
  -- minusDiffDomain
  constructor
  · kernel_decide
  -- plusDiffDomain
  constructor
  · kernel_decide
  -- minusCorrection
  constructor
  · kernel_decide
  -- plusCorrection
  constructor
  · kernel_decide
  -- qCap_positive
  constructor
  · kernel_decide
  -- qCap_derivative_lower
  constructor
  · kernel_decide
  -- qCap_le_domain
  constructor
  · kernel_decide
  -- rCap_positive
  constructor
  · kernel_decide
  -- rCap_le_three
  constructor
  · kernel_decide
  -- api
  constructor
  · kernel_decide
  -- qmax
  constructor
  · kernel_decide
  -- rmax
  constructor
  · kernel_decide
  -- rltq
  constructor
  · kernel_decide
  -- qcap
  constructor
  · kernel_decide
  -- rcap
  constructor
  · kernel_decide
  -- ceff
  constructor
  · kernel_decide
  -- corner (five independently cached semantic components)
  constructor
  · apply uniformPositive_affineCorner_of_lower_components
      (prefactorLower := prefactorLower_169)
      (qCorrectionLower := cap294CorrectionLower)
      (rCorrectionLower := cap169CorrectionLower)
      (penaltyLower := penaltyLower_169)
      (sincGapLower := sincGapLower_169)
    · exact prefactor_169
    · apply uniformLower_of_evalLower
      change EvalLower (data ⟨169, by decide⟩).boxes
        (circleCorrectionLowerE scalarLogTerms scalarTrigDoubles
          scalarFourierTerms (.rat (294 / 100)) piE)
        cap294CorrectionLower
      exact cap294Correction (data ⟨169, by decide⟩)
    · apply uniformLower_of_evalLower
      change EvalLower (data ⟨169, by decide⟩).boxes
        (circleCorrectionLowerE scalarLogTerms scalarTrigDoubles
          scalarFourierTerms (.rat (169 / 100)) piE)
        cap169CorrectionLower
      exact cap169Correction (data ⟨169, by decide⟩)
    · exact penalty_169
    · exact sincGap_169
    · kernel_decide
  -- r_eval
  constructor
  · kernel_decide
  -- q_eval
  constructor
  · kernel_decide
  -- domain_lo_le
  constructor
  · kernel_decide
  -- q_hi_le
  constructor
  · kernel_decide
  -- derivative
  · intro j
    fin_cases j <;> kernel_decide

end Erdos1038.HighKPlatformAffineTableChunk169
