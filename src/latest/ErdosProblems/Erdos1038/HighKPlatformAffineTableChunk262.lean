import ErdosProblems.Erdos1038.HighKPlatformAffineTableData
import ErdosProblems.Erdos1038.HighKPlatformAffineCorrectionCertificateCap172
import ErdosProblems.Erdos1038.HighKPlatformAffineCorrectionCertificateCap283
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerPrefactorChunk262
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerPenaltyChunk262
import ErdosProblems.Erdos1038.HighKPlatformAffineCornerSincGapChunk262
import ErdosProblems.Erdos1038.KernelDecision

/-! Generated proof-producing checks for affine-table cells. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineTableChunk262

open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineTableData
open Erdos1038 HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCornerComponents
open Erdos1038.HighKPlatformAffineSemanticCorner
open Erdos1038.HighKPlatformAffineCornerLeafCertificates
open Erdos1038.HighKPlatformAffineCorrectionCertificates

theorem raw_262 : RawChecks (data ⟨262, by decide⟩) := by
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
      (prefactorLower := prefactorLower_262)
      (qCorrectionLower := cap283CorrectionLower)
      (rCorrectionLower := cap172CorrectionLower)
      (penaltyLower := penaltyLower_262)
      (sincGapLower := sincGapLower_262)
    · exact prefactor_262
    · apply uniformLower_of_evalLower
      change EvalLower (data ⟨262, by decide⟩).boxes
        (circleCorrectionLowerE scalarLogTerms scalarTrigDoubles
          scalarFourierTerms (.rat (283 / 100)) piE)
        cap283CorrectionLower
      exact cap283Correction (data ⟨262, by decide⟩)
    · apply uniformLower_of_evalLower
      change EvalLower (data ⟨262, by decide⟩).boxes
        (circleCorrectionLowerE scalarLogTerms scalarTrigDoubles
          scalarFourierTerms (.rat (172 / 100)) piE)
        cap172CorrectionLower
      exact cap172Correction (data ⟨262, by decide⟩)
    · exact penalty_262
    · exact sincGap_262
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

end Erdos1038.HighKPlatformAffineTableChunk262
