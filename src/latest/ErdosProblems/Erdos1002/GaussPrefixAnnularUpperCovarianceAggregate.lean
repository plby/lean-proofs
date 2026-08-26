import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFrozenJoint
import ErdosProblems.Erdos1002.GaussPrefixAnnularLateGeometricDomination
import ErdosProblems.Erdos1002.GaussPrefixAnnularLateErrorAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Aggregate prefix--future covariance for contracted upper tuples

After prefix and density freezing, every contracted upper tuple is an
exact instance of the functional Gauss prefix--future mixing theorem.  Its
prefix cutoff is the delayed depth and its future block begins after the
residual delayed mixing gap.  This file sums the resulting covariance
bound without discarding any prefix factor or future coordinate.

The number of tuples is polynomial in the ambient depth, while the
residual gap tends to infinity and controls that ambient depth linearly.
Consequently the exponentially small mixing rate dominates the complete
contracted tagged family.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 800000

local instance gaussPrefixAnnularUpperCovarianceAggregatePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## One-tag covariance -/

/-- Functional prefix--future mixing for one contracted upper tag, with
the literal delayed depth, residual gap, denominator-good word set, and
complete future digit block. -/
theorem
    norm_annularContractedUpperRetainedFrozenDigitJoint_sub_factorized_le
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    ‖annularContractedUpperRetainedFrozenDigitJoint
          ε A eta rho N k hr mode hmode p -
        annularContractedUpperRetainedFrozenPrefixMean
            ε A eta rho N k hr mode hmode p *
          annularContractedUpperRetainedFutureMean
            ε A eta rho N k hr mode hmode p‖ ≤
      (384 * Real.log 2) *
        (527 / 540 : ℝ) ^
          annularContractedUpperRetainedMixingGap rho N := by
  have hEvents :
      ∀ j : Fin (MixedOccurrenceCount k),
        MeasurableSet
          (annularContractedUpperRetainedFutureDigitEvent
            ε A p j) := by
    intro j
    unfold annularContractedUpperRetainedFutureDigitEvent
      annularContractedUpperRetainedUpperTag
    exact
      measurableSet_annularUpperRetainedFutureDigitEvent
        (annularContractedUpperRetainedToUpper p) j
  simpa only [
      annularContractedUpperRetainedFrozenDigitJoint,
      annularContractedUpperRetainedFrozenPrefixMean,
      annularContractedUpperRetainedFutureMean] using!
    gaussLateLebesgueWeightedFrozen_covariance_le_commonGap
      N
      (activeAnnularOccurrenceSignedLower k ε A)
      (activeAnnularOccurrenceSignedUpper k ε A)
      k
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularContractedUpperRetainedRealization p).1
      (annularContractedUpperRetainedDelayedDepth p)
      (annularContractedUpperRetainedMixingGap rho N)
      (annularContractedUpperRetainedMixingGap rho N)
      (by rfl)
      (annularContractedUpperRetainedGoodWords eta rho N p)
      (annularContractedUpperRetainedFutureTime p)
      hEvents

/-! ## Cardinality of the contracted tagged family -/

/-- The cardinality of the contracted tagged sigma type is exactly the
nested pair count over chronological labels and contracted tuple
families. -/
theorem card_annularContractedUpperRetainedTaggedTuple_eq_nestedPairCount
    (eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Fintype.card
        (AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode) =
      nestedPairCount
        (Finset.univ :
          Finset (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k))
        (fun e ↦
          contractedAnnularCanonicalLaterUpperMidpointTupleFamily
            eta rho N k hr e (mode e) (hmode e)) := by
  simp [AnnularContractedUpperRetainedTaggedTuple,
    nestedPairCount]

/-- Contracting the deterministic time boxes cannot increase the tagged
pair count. -/
theorem
    nestedPairCount_contractedAnnularUpperRetained_le_upperRetained
    (eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    nestedPairCount
        (Finset.univ :
          Finset (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k))
        (fun e ↦
          contractedAnnularCanonicalLaterUpperMidpointTupleFamily
            eta rho N k hr e (mode e) (hmode e)) ≤
      nestedPairCount
        (Finset.univ :
          Finset (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k))
        (fun e ↦
          annularCanonicalLaterUpperMidpointTupleFamily
            rho N k hr e (mode e) (hmode e)) := by
  unfold nestedPairCount
  apply Finset.sum_le_sum
  intro e _he
  exact Finset.card_le_card
    (contractedAnnularCanonicalLaterUpperMidpointTupleFamily_subset_upper
      k hr e (mode e) (hmode e))

/-- The contracted tagged family has the same eventual ambient-polynomial
cardinality bound as the full upper-retained family. -/
theorem
    eventually_nestedPairCount_contractedAnnularUpperRetained_le_ambient_pow
    (eta rho : ℝ) {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      nestedPairCount
          (Finset.univ :
            Finset (Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k))
          (fun e ↦
            contractedAnnularCanonicalLaterUpperMidpointTupleFamily
              eta rho N k hr e (mode e) (hmode e)) ≤
        annularDepthAmbientSize N ^
          (MixedOccurrenceCount k + 1) := by
  filter_upwards
    [eventually_nestedPairCount_annularUpperRetained_le_ambient_pow_succ
      (rho := rho) hgrid k hr htime mode hmode] with N hN
  exact
    (nestedPairCount_contractedAnnularUpperRetained_le_upperRetained
      eta rho N k hr mode hmode).trans hN

/-! ## Aggregate norm sum -/

/-- Sum of the absolute covariance errors over every contracted upper
tag.  The norm is deliberately inside the finite sum. -/
def annularContractedUpperRetainedFrozenCovarianceNormSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℝ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    ‖annularContractedUpperRetainedFrozenDigitJoint
          ε A eta rho N k hr mode hmode p -
        annularContractedUpperRetainedFrozenPrefixMean
            ε A eta rho N k hr mode hmode p *
          annularContractedUpperRetainedFutureMean
            ε A eta rho N k hr mode hmode p‖

/-- Finite-`N` domination by the tagged cardinality times the uniform
functional-mixing rate. -/
theorem
    annularContractedUpperRetainedFrozenCovarianceNormSum_le
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    annularContractedUpperRetainedFrozenCovarianceNormSum
        ε A eta rho N k hr mode hmode ≤
      (Fintype.card
        (AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode) : ℝ) *
        ((384 * Real.log 2) *
          (527 / 540 : ℝ) ^
            annularContractedUpperRetainedMixingGap rho N) := by
  unfold annularContractedUpperRetainedFrozenCovarianceNormSum
  calc
    (∑ p : AnnularContractedUpperRetainedTaggedTuple
        eta rho N k hr mode hmode,
      ‖annularContractedUpperRetainedFrozenDigitJoint
            ε A eta rho N k hr mode hmode p -
          annularContractedUpperRetainedFrozenPrefixMean
              ε A eta rho N k hr mode hmode p *
            annularContractedUpperRetainedFutureMean
              ε A eta rho N k hr mode hmode p‖) ≤
        ∑ _p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          ((384 * Real.log 2) *
            (527 / 540 : ℝ) ^
              annularContractedUpperRetainedMixingGap rho N) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact
        norm_annularContractedUpperRetainedFrozenDigitJoint_sub_factorized_le
          ε A eta rho N k hr mode hmode p
    _ = _ := by simp

/-- Polynomially many contracted upper covariance errors are killed by
the residual delayed mixing gap. -/
theorem
    tendsto_annularContractedUpperRetainedFrozenCovarianceNormSum_zero
    {rho : ℝ} (hrho : 0 < rho)
    (ε A eta : ℝ)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N ↦
        annularContractedUpperRetainedFrozenCovarianceNormSum
          ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  let prefixes :
      ℕ → Finset
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) :=
    fun _N ↦ Finset.univ
  let futures :
      ℕ →
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) →
        Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
    fun N e ↦
      contractedAnnularCanonicalLaterUpperMidpointTupleFamily
        eta rho N k hr e (mode e) (hmode e)
  let gap : ℕ → ℕ :=
    annularContractedUpperRetainedMixingGap rho
  let rate : ℕ → ℝ := fun N ↦
    (384 * Real.log 2) *
      (527 / 540 : ℝ) ^ gap N
  have hmajor :
      Tendsto
        (fun N ↦
          ∑ e ∈ prefixes N, ∑ _t ∈ futures N e, rate N)
        atTop (nhds 0) := by
    apply
      tendsto_nested_nonnegative_sum_zero_of_pairCount_le_scalePow_inverseGeometric
        prefixes futures (fun N _e _t ↦ rate N)
        annularDepthAmbientSize gap
        (tendsto_annularUpperRetainedDelayedMixingGap_atTop hrho)
        (MixedOccurrenceCount k + 1)
        (2 * ⌈2 / rho⌉₊)
        (C := 384 * Real.log 2)
        (theta := 540 / 527)
        (by positivity)
        (by norm_num)
    · exact Eventually.of_forall fun N ↦
        annularDepthAmbientSize_le_two_natCeil_two_div_rho_mul_delayedGap_add_one
          hrho N
    · simpa only [prefixes, futures] using!
        eventually_nestedPairCount_contractedAnnularUpperRetained_le_ambient_pow
          eta rho hgrid k hr htime mode hmode
    · intro N _e _t
      dsimp only [rate]
      positivity
    · filter_upwards with N
      intro e _he t _ht
      dsimp only [rate, gap]
      rw [show (527 / 540 : ℝ) =
        (540 / 527 : ℝ)⁻¹ by norm_num, inv_pow]
  have hupper :
      ∀ᶠ N : ℕ in atTop,
        annularContractedUpperRetainedFrozenCovarianceNormSum
            ε A eta rho N k hr mode hmode ≤
          ∑ e ∈ prefixes N, ∑ _t ∈ futures N e, rate N := by
    filter_upwards with N
    have hcov :=
      annularContractedUpperRetainedFrozenCovarianceNormSum_le
        ε A eta rho N k hr mode hmode
    calc
      annularContractedUpperRetainedFrozenCovarianceNormSum
          ε A eta rho N k hr mode hmode ≤
        (Fintype.card
          (AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode) : ℝ) * rate N := by
          simpa only [rate, gap] using! hcov
      _ =
        ∑ e ∈ prefixes N, ∑ _t ∈ futures N e, rate N := by
          rw [
            card_annularContractedUpperRetainedTaggedTuple_eq_nestedPairCount]
          simp only [prefixes, futures, nestedPairCount, rate,
            Finset.sum_const, nsmul_eq_mul, Nat.cast_sum]
          rw [Finset.sum_mul]
  exact squeeze_zero'
    (Eventually.of_forall fun _N ↦ by
      unfold annularContractedUpperRetainedFrozenCovarianceNormSum
      exact Finset.sum_nonneg fun _p _hp ↦ norm_nonneg _)
    hupper hmajor

/-! ## Difference of the aggregate frozen and factorized sums -/

/-- Aggregate frozen joint before covariance factorization. -/
def annularContractedUpperRetainedFrozenDigitJointSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    annularContractedUpperRetainedFrozenDigitJoint
      ε A eta rho N k hr mode hmode p

/-- Aggregate product of frozen prefix and future means. -/
def annularContractedUpperRetainedFactorizedMeanSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    annularContractedUpperRetainedFrozenPrefixMean
        ε A eta rho N k hr mode hmode p *
      annularContractedUpperRetainedFutureMean
        ε A eta rho N k hr mode hmode p

/-- The aggregate frozen joint and the aggregate product of its two means
differ by at most the sum of the individual covariance norms. -/
theorem
    norm_annularContractedUpperRetainedFrozenDigitJointSum_sub_factorized_le
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    ‖annularContractedUpperRetainedFrozenDigitJointSum
          ε A eta rho N k hr mode hmode -
        annularContractedUpperRetainedFactorizedMeanSum
          ε A eta rho N k hr mode hmode‖ ≤
      annularContractedUpperRetainedFrozenCovarianceNormSum
        ε A eta rho N k hr mode hmode := by
  unfold annularContractedUpperRetainedFrozenDigitJointSum
    annularContractedUpperRetainedFactorizedMeanSum
    annularContractedUpperRetainedFrozenCovarianceNormSum
  rw [← Finset.sum_sub_distrib]
  exact norm_sum_le _ _

/-- Aggregate covariance factorization error tends to zero. -/
theorem
    tendsto_annularContractedUpperRetainedFrozenDigitJointSum_sub_factorized_zero
    {rho : ℝ} (hrho : 0 < rho)
    (ε A eta : ℝ)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N ↦
        annularContractedUpperRetainedFrozenDigitJointSum
            ε A eta rho N k hr mode hmode -
          annularContractedUpperRetainedFactorizedMeanSum
            ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  have hnorm :=
    tendsto_annularContractedUpperRetainedFrozenCovarianceNormSum_zero
      hrho ε A eta hgrid k hr htime mode hmode
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _N ↦ norm_nonneg _)
    (Eventually.of_forall fun N ↦
      norm_annularContractedUpperRetainedFrozenDigitJointSum_sub_factorized_le
        ε A eta rho N k hr mode hmode)
    hnorm

end

end Erdos1002
