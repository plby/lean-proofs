import ErdosProblems.Erdos1002.GaussPrefixAnnularLateJointReplacement
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperContracted

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Joint future replacement on the contracted upper family

The heterogeneous exact-to-digit estimate was proved for the complete
upper-retained family.  A time-box contraction only removes tuples.
Because the replacement error is the nonnegative measure of a symmetric
difference, the complete-intersection estimate passes monotonically to
the contracted family.  This file records that passage explicitly.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology symmDiff

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularContractedJointReplacementPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- Complete exact-to-future-digit replacement error after contracting all
deterministic time boxes.  Every prefix exact window is still present in
both events; only genuine future coordinates are digitized. -/
def aggregateContractedAnnularUpperRetainedJointFutureReplacementError
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℝ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    ∑ t ∈ contractedAnnularCanonicalLaterUpperMidpointTupleFamily
        eta rho N k hr e (mode e) (hmode e),
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
              (Real.log (N : ℝ))
              (gaussPrescribedParityOrientedLower
                (flattenedAnnularParity e)
                (flattenedAnnularSignedLower ε A e)
                (flattenedAnnularSignedUpper ε A e))
              (gaussPrescribedParityOrientedUpper
                (flattenedAnnularParity e)
                (flattenedAnnularSignedLower ε A e)
                (flattenedAnnularSignedUpper ε A e)) t ∆
          annularUpperRetainedMaskedApproximationDigitEvent
            ε A N e (mode e) (hmode e) t)

/-- Contracting the time boxes cannot increase the complete joint
replacement error. -/
theorem
    aggregateContractedAnnularUpperRetainedJointFutureReplacementError_le
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    aggregateContractedAnnularUpperRetainedJointFutureReplacementError
        ε A eta rho N k hr mode hmode ≤
      aggregateAnnularUpperRetainedJointFutureReplacementError
        ε A rho N k hr mode hmode := by
  unfold
    aggregateContractedAnnularUpperRetainedJointFutureReplacementError
    aggregateAnnularUpperRetainedJointFutureReplacementError
  apply Finset.sum_le_sum
  intro e _he
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact
      contractedAnnularCanonicalLaterUpperMidpointTupleFamily_subset_upper
        k hr e (mode e) (hmode e)
  · intro _t _ht _hnot
    exact measureReal_nonneg

/-- For every fixed contraction, the complete contracted replacement
error tends to zero.  The proof is a monotone restriction of the
full-tuple replacement theorem, so no prefix rare factor is discarded. -/
theorem
    tendsto_contractedAnnularUpperRetained_jointFutureReplacement_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (eta rho : ℝ) {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N ↦
        aggregateContractedAnnularUpperRetainedJointFutureReplacementError
          ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  have hfull :=
    tendsto_annularUpperRetained_jointFutureReplacement_zero
      hε hεA rho hgrid k hr htime hsigned mode hmode
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦ by
      unfold
        aggregateContractedAnnularUpperRetainedJointFutureReplacementError
      exact Finset.sum_nonneg fun _e _he ↦
        Finset.sum_nonneg fun _t _ht ↦ measureReal_nonneg
  · exact Eventually.of_forall fun N ↦
      aggregateContractedAnnularUpperRetainedJointFutureReplacementError_le
        ε A eta rho N k hr mode hmode
  · exact hfull

end

end Erdos1002
