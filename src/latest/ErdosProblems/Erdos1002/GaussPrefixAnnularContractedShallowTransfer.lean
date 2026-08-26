import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperGoodTransfer
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperShallowVariableTolerance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Restricting shallow upper cancellation to contracted tuples

The time-box contraction only deletes upper-retained tuples.  This module
records the literal injection from contracted tagged tuples into all
upper-retained tagged tuples and transfers the already-proved absolute
shallow-prefix cancellation to that subfamily.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 800000

local instance gaussPrefixAnnularContractedShallowTransferPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- Forgetting the proof of time-box contraction is injective. -/
theorem annularContractedUpperRetainedToUpper_injective
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0} :
    Function.Injective
      (annularContractedUpperRetainedToUpper :
        AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode →
          AnnularUpperRetainedTaggedTuple
            rho N k hr mode hmode) := by
  intro p q hpq
  rcases p with ⟨e, t⟩
  rcases q with ⟨e', t'⟩
  have he : e = e' := congrArg Sigma.fst hpq
  subst e'
  have ht : t.1 = t'.1 :=
    congrArg (fun u ↦ u.2.1) hpq
  have htt : t = t' := Subtype.ext ht
  subst t'
  rfl

/-- The shallow integral attached to a contracted tag is exactly the
uncontracted shallow integral of its image. -/
def annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
    (ε A eta rho Delta : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  annularUpperRetainedShallowPrefixGoodIntegralWithTolerance
    ε A rho Delta N k hr mode hmode
    (annularContractedUpperRetainedToUpper p)

/-- At every finite scale, the absolute shallow sum on contracted tags is
bounded by the absolute shallow sum on the full upper-retained family. -/
theorem
    sum_norm_annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance_le
    (ε A eta rho Delta : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    (∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        ‖annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
          ε A eta rho Delta N k hr mode hmode p‖) ≤
      ∑ p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode,
        ‖annularUpperRetainedShallowPrefixGoodIntegralWithTolerance
          ε A rho Delta N k hr mode hmode p‖ := by
  let f :
      AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode →
        AnnularUpperRetainedTaggedTuple rho N k hr mode hmode :=
    annularContractedUpperRetainedToUpper
  let g :
      AnnularUpperRetainedTaggedTuple rho N k hr mode hmode → ℝ :=
    fun p ↦
      ‖annularUpperRetainedShallowPrefixGoodIntegralWithTolerance
        ε A rho Delta N k hr mode hmode p‖
  have hf : Function.Injective f :=
    annularContractedUpperRetainedToUpper_injective
  calc
    (∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        ‖annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
          ε A eta rho Delta N k hr mode hmode p‖) =
        ∑ p ∈ (Finset.univ :
            Finset (AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode)),
          g (f p) := by
      simp only [
        annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance,
        f, g]
    _ = ∑ q ∈
          (Finset.univ :
              Finset (AnnularContractedUpperRetainedTaggedTuple
                eta rho N k hr mode hmode)).image f,
        g q := by
      rw [Finset.sum_image]
      exact hf.injOn
    _ ≤ ∑ q : AnnularUpperRetainedTaggedTuple
          rho N k hr mode hmode, g q :=
      Finset.sum_le_univ_sum_of_nonneg
        (fun q ↦ norm_nonneg
          (annularUpperRetainedShallowPrefixGoodIntegralWithTolerance
            ε A rho Delta N k hr mode hmode q))
    _ = ∑ p : AnnularUpperRetainedTaggedTuple
          rho N k hr mode hmode,
        ‖annularUpperRetainedShallowPrefixGoodIntegralWithTolerance
          ε A rho Delta N k hr mode hmode p‖ := by
      rfl

/-- Hence the contracted shallow absolute sum vanishes at every fixed
admissible tolerance. -/
theorem
    tendsto_sum_norm_annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance_zero
    {ε A eta rho Delta : ℝ}
    (hε : 0 < ε) (hεA : ε < A) (hrho : 0 < rho)
    (hDelta : 0 ≤ Delta)
    (hDeltaUpper :
      Delta ≤ upperRetainedShallowDenominatorTolerance rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        ∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          ‖annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance
            ε A eta rho Delta N k hr mode hmode p‖)
      atTop (nhds 0) := by
  have hfull :=
    tendsto_sum_norm_annularUpperRetainedShallowPrefixGoodIntegralWithTolerance_zero
      hε hεA hrho hDelta hDeltaUpper hgrid k hr htime hsigned
      mode hmode
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦
      Finset.sum_nonneg fun _p _hp ↦ norm_nonneg _
  · exact Eventually.of_forall fun N ↦
      sum_norm_annularContractedUpperRetainedShallowPrefixGoodIntegralWithTolerance_le
        ε A eta rho Delta N k hr mode hmode
  · exact hfull

end

end Erdos1002
