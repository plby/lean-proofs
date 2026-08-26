import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFrozenJoint
import ErdosProblems.Erdos1002.GaussPrefixAnnularContractedJointReplacement
import ErdosProblems.Erdos1002.GaussPrefixAnnularMaskedEventBridge
import ErdosProblems.Erdos1002.GaussPrefixAnnularDelayedFreezing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Localized future-digit transfer for contracted upper annular tuples

The delayed-prefix-good character still contains the literal marked event
at every selected future depth.  Replacing that future block by a digit
block is therefore not a bare symmetric-difference argument: away from the
global denominator-good event the literal future event also contains a
denominator cutoff which the approximation event does not see.

This file keeps that distinction explicit.  On the global denominator-good
event, the literal marked tuple and the complete oriented approximation
tuple agree, so the pointwise replacement is controlled by the complete
exact/masked symmetric difference.  On the complement, both integrands are
bounded by the same homogeneous approximation-window count.  The first
aggregate tends to zero by the joint replacement theorem and the second by
the already proved bad-event moment estimate.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology symmDiff

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 1000000

local instance gaussPrefixAnnularUpperDigitTransferPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## Aggregate live joint -/

/-- The aggregate of the live delayed-prefix characters with the complete
future digit block still attached. -/
def annularContractedUpperRetainedLiveDigitJointSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    annularContractedUpperRetainedLiveDigitJoint
      ε A eta rho N k hr mode hmode p

/-! ## Generic localized aggregate estimate -/

/-- A finite-family comparison in which the two integrands need only be
close, rather than equal, on the good event.  The on-good error is charged
to a measurable exceptional set for each tag; on the complement both
integrands are bounded by a common event indicator. -/
theorem norm_sum_integral_sub_le_error_add_goodCompl_indicatorSum
    {α ι : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsFiniteMeasure mu]
    (s : Finset ι) (good : Set α) (hgood : MeasurableSet good)
    (error envelope : ι → Set α)
    (herror : ∀ i ∈ s, MeasurableSet (error i))
    (henvelope : ∀ i ∈ s, MeasurableSet (envelope i))
    (f g : ι → α → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i) mu)
    (hg : ∀ i ∈ s, Integrable (g i) mu)
    (hclose :
      ∀ᵐ x ∂mu, x ∈ good → ∀ i ∈ s,
        ‖f i x - g i x‖ ≤
          (error i).indicator (fun _x ↦ (1 : ℝ)) x)
    (hbound :
      ∀ᵐ x ∂mu, ∀ i ∈ s,
        ‖f i x‖ ≤
            (envelope i).indicator (fun _x ↦ (1 : ℝ)) x ∧
          ‖g i x‖ ≤
            (envelope i).indicator (fun _x ↦ (1 : ℝ)) x) :
    ‖∑ i ∈ s,
        ((∫ x, f i x ∂mu) - ∫ x, g i x ∂mu)‖ ≤
      (∑ i ∈ s, mu.real (error i)) +
        ∫ x in goodᶜ,
          2 * ∑ i ∈ s,
            (envelope i).indicator (fun _x ↦ (1 : ℝ)) x ∂mu := by
  let q : α → ℂ := fun x ↦
    ∑ i ∈ s, (f i x - g i x)
  let errCount : α → ℝ := fun x ↦
    ∑ i ∈ s, (error i).indicator (fun _x ↦ (1 : ℝ)) x
  let envelopeCount : α → ℝ := fun x ↦
    ∑ i ∈ s, (envelope i).indicator (fun _x ↦ (1 : ℝ)) x
  have hqInt : Integrable q mu := by
    dsimp only [q]
    apply integrable_finset_sum
    intro i hi
    exact (hf i hi).sub (hg i hi)
  have herrCountInt : Integrable errCount mu := by
    dsimp only [errCount]
    apply integrable_finset_sum
    intro i hi
    exact (integrable_const (1 : ℝ)).indicator (herror i hi)
  have henvelopeCountInt : Integrable envelopeCount mu := by
    dsimp only [envelopeCount]
    apply integrable_finset_sum
    intro i hi
    exact (integrable_const (1 : ℝ)).indicator (henvelope i hi)
  have hmajorInt :
      Integrable
        (fun x ↦ errCount x +
          goodᶜ.indicator (fun y ↦ 2 * envelopeCount y) x) mu :=
    herrCountInt.add
      ((henvelopeCountInt.const_mul 2).indicator hgood.compl)
  have hsumIntegral :
      (∑ i ∈ s,
          ((∫ x, f i x ∂mu) - ∫ x, g i x ∂mu)) =
        ∫ x, q x ∂mu := by
    calc
      (∑ i ∈ s,
          ((∫ x, f i x ∂mu) - ∫ x, g i x ∂mu)) =
          ∑ i ∈ s, ∫ x, (f i x - g i x) ∂mu := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_sub (hf i hi) (hg i hi)]
      _ = ∫ x, q x ∂mu := by
        dsimp only [q]
        rw [integral_finset_sum]
        intro i hi
        exact (hf i hi).sub (hg i hi)
  rw [hsumIntegral]
  calc
    ‖∫ x, q x ∂mu‖ ≤ ∫ x, ‖q x‖ ∂mu :=
      norm_integral_le_integral_norm q
    _ ≤ ∫ x,
        errCount x +
          goodᶜ.indicator (fun y ↦ 2 * envelopeCount y) x ∂mu := by
      apply integral_mono_ae hqInt.norm hmajorInt
      filter_upwards [hclose, hbound] with x hclosex hboundx
      by_cases hx : x ∈ good
      · have hxCompl : x ∉ goodᶜ := by
          simpa only [Set.mem_compl_iff, not_not] using! hx
        rw [Set.indicator_of_notMem hxCompl, add_zero]
        calc
          ‖q x‖ ≤ ∑ i ∈ s, ‖f i x - g i x‖ := by
            dsimp only [q]
            exact norm_sum_le _ _
          _ ≤ ∑ i ∈ s,
              (error i).indicator (fun _x ↦ (1 : ℝ)) x := by
            apply Finset.sum_le_sum
            intro i hi
            exact hclosex hx i hi
          _ = errCount x := rfl
      · rw [Set.indicator_of_mem (by
          simpa only [Set.mem_compl_iff] using! hx)]
        have herrNonneg : 0 ≤ errCount x := by
          dsimp only [errCount]
          exact Finset.sum_nonneg fun i _hi ↦
            Set.indicator_nonneg (fun _x ↦ by norm_num) x
        calc
          ‖q x‖ ≤ ∑ i ∈ s, ‖f i x - g i x‖ := by
            dsimp only [q]
            exact norm_sum_le _ _
          _ ≤ ∑ i ∈ s, (‖f i x‖ + ‖g i x‖) := by
            apply Finset.sum_le_sum
            intro i hi
            exact norm_sub_le _ _
          _ ≤ ∑ i ∈ s,
              ((envelope i).indicator (fun _x ↦ (1 : ℝ)) x +
                (envelope i).indicator (fun _x ↦ (1 : ℝ)) x) := by
            apply Finset.sum_le_sum
            intro i hi
            exact add_le_add (hboundx i hi).1 (hboundx i hi).2
          _ = 2 * envelopeCount x := by
            dsimp only [envelopeCount]
            rw [Finset.sum_add_distrib]
            ring
          _ ≤ errCount x + 2 * envelopeCount x := by
            linarith
    _ =
      (∑ i ∈ s, mu.real (error i)) +
        ∫ x in goodᶜ,
          2 * ∑ i ∈ s,
            (envelope i).indicator (fun _x ↦ (1 : ℝ)) x ∂mu := by
      rw [integral_add herrCountInt
        ((henvelopeCountInt.const_mul 2).indicator hgood.compl)]
      congr 1
      · dsimp only [errCount]
        rw [integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro i hi
          exact integral_indicator_one (herror i hi)
        · intro i hi
          exact (integrable_const (1 : ℝ)).indicator (herror i hi)
      · rw [integral_indicator hgood.compl]

/-- A union envelope on a bad set separates into its primary-event
integral and twice the total measure of the exceptional events.  The
exceptional part is enlarged from the bad set to the whole space, which
is legitimate because its indicator sum is nonnegative. -/
theorem setIntegral_two_sum_unionIndicator_le
    {α ι : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsFiniteMeasure mu]
    (s : Finset ι) (bad : Set α)
    (primary error : ι → Set α)
    (hprimary : ∀ i ∈ s, MeasurableSet (primary i))
    (herror : ∀ i ∈ s, MeasurableSet (error i)) :
    (∫ x in bad,
        2 * ∑ i ∈ s,
          (primary i ∪ error i).indicator
            (fun _x ↦ (1 : ℝ)) x ∂mu) ≤
      (∫ x in bad,
        2 * ∑ i ∈ s,
          (primary i).indicator
            (fun _x ↦ (1 : ℝ)) x ∂mu) +
        2 * ∑ i ∈ s, mu.real (error i) := by
  let primaryCount : α → ℝ := fun x ↦
    ∑ i ∈ s, (primary i).indicator (fun _x ↦ (1 : ℝ)) x
  let errorCount : α → ℝ := fun x ↦
    ∑ i ∈ s, (error i).indicator (fun _x ↦ (1 : ℝ)) x
  let unionCount : α → ℝ := fun x ↦
    ∑ i ∈ s, (primary i ∪ error i).indicator
      (fun _x ↦ (1 : ℝ)) x
  have hprimaryInt : Integrable primaryCount mu := by
    dsimp only [primaryCount]
    apply integrable_finset_sum
    intro i hi
    exact (integrable_const (1 : ℝ)).indicator (hprimary i hi)
  have herrorInt : Integrable errorCount mu := by
    dsimp only [errorCount]
    apply integrable_finset_sum
    intro i hi
    exact (integrable_const (1 : ℝ)).indicator (herror i hi)
  have hunionInt : Integrable unionCount mu := by
    dsimp only [unionCount]
    apply integrable_finset_sum
    intro i hi
    exact (integrable_const (1 : ℝ)).indicator
      ((hprimary i hi).union (herror i hi))
  have hpoint : ∀ x, 2 * unionCount x ≤
      2 * primaryCount x + 2 * errorCount x := by
    intro x
    have hsum : unionCount x ≤ primaryCount x + errorCount x := by
      dsimp only [unionCount, primaryCount, errorCount]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      by_cases hxPrimary : x ∈ primary i <;>
        by_cases hxError : x ∈ error i <;>
          simp [Set.indicator, hxPrimary, hxError]
    linarith
  calc
    (∫ x in bad, 2 * unionCount x ∂mu) ≤
        ∫ x in bad,
          (2 * primaryCount x + 2 * errorCount x) ∂mu := by
      apply integral_mono
        ((hunionInt.const_mul 2).mono_measure Measure.restrict_le_self)
        (((hprimaryInt.const_mul 2).add
          (herrorInt.const_mul 2)).mono_measure Measure.restrict_le_self)
      exact hpoint
    _ =
        (∫ x in bad, 2 * primaryCount x ∂mu) +
          ∫ x in bad, 2 * errorCount x ∂mu := by
      rw [integral_add
        ((hprimaryInt.const_mul 2).mono_measure Measure.restrict_le_self)
        ((herrorInt.const_mul 2).mono_measure Measure.restrict_le_self)]
    _ ≤
        (∫ x in bad, 2 * primaryCount x ∂mu) +
          ∫ x, 2 * errorCount x ∂mu := by
      exact add_le_add_right
        (setIntegral_le_integral (herrorInt.const_mul 2)
          (Eventually.of_forall fun x ↦ by
            have hnonneg : 0 ≤ errorCount x := by
              dsimp only [errorCount]
              exact Finset.sum_nonneg fun i _hi ↦
                Set.indicator_nonneg (fun _x ↦ by norm_num) x
            simpa only [Pi.zero_apply] using!
              mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnonneg))
        _
    _ =
        (∫ x in bad, 2 * primaryCount x ∂mu) +
          2 * ∑ i ∈ s, mu.real (error i) := by
      congr 1
      rw [integral_const_mul]
      congr 1
      dsimp only [errorCount]
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i hi
        exact integral_indicator_one (herror i hi)
      · intro i hi
        exact (integrable_const (1 : ℝ)).indicator (herror i hi)

/-! ## Exact event identities for one contracted tag -/

/-- For a canonical contracted tag, the signed tuple event is literally
the parity-oriented heterogeneous event used by the masked replacement
estimate. -/
theorem
    annularContractedUpperRetained_signedTupleEvent_eq_exactTupleEvent
    {ε A eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    gaussSignedApproximationTupleEvent
        (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A p.1)
        (flattenedAnnularSignedUpper ε A p.1)
        (annularContractedUpperRetainedTimes p) =
      gaussHeterogeneousApproximationTupleEvent
        (Real.log (N : ℝ))
        (gaussPrescribedParityOrientedLower
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1))
        (gaussPrescribedParityOrientedUpper
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1))
        (annularContractedUpperRetainedTimes p) := by
  rw [gaussSignedApproximationTupleEvent_eq_oriented]
  have hlower :
      (fun j ↦
        gaussParityOrientedLower
          (annularContractedUpperRetainedTimes p j)
          (flattenedAnnularSignedLower ε A p.1 j)
          (flattenedAnnularSignedUpper ε A p.1 j)) =
        gaussPrescribedParityOrientedLower
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1) := by
    funext j
    apply gaussParityOrientedLower_eq_of_mod_two_eq
    rw [Nat.mod_eq_of_lt (flattenedAnnularParity p.1 j).isLt]
    exact annularContractedUpperRetainedTimes_parity p j
  have hupper :
      (fun j ↦
        gaussParityOrientedUpper
          (annularContractedUpperRetainedTimes p j)
          (flattenedAnnularSignedLower ε A p.1 j)
          (flattenedAnnularSignedUpper ε A p.1 j)) =
        gaussPrescribedParityOrientedUpper
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1) := by
    funext j
    apply gaussParityOrientedUpper_eq_of_mod_two_eq
    rw [Nat.mod_eq_of_lt (flattenedAnnularParity p.1 j).isLt]
    exact annularContractedUpperRetainedTimes_parity p j
  rw [hlower, hupper]

/-- Contracted form of the exact prefix--future event decomposition. -/
theorem
    annularContractedUpperRetained_exactTupleEvent_eq_prefix_inter_future
    {ε A eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    gaussHeterogeneousApproximationTupleEvent
        (Real.log (N : ℝ))
        (gaussPrescribedParityOrientedLower
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1))
        (gaussPrescribedParityOrientedUpper
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1))
        (annularContractedUpperRetainedTimes p) =
      annularUpperRetainedPrefixApproximationEvent ε A
          (annularContractedUpperRetainedToUpper p) ∩
        annularUpperRetainedFutureApproximationEvent ε A
          (annularContractedUpperRetainedToUpper p) := by
  simpa only [annularUpperRetainedOrientedLower,
    annularUpperRetainedOrientedUpper,
    annularContractedUpperRetainedTimes_embedding] using!
    (annularUpperRetained_exactTupleEvent_eq_prefix_inter_futureApproximation
      (ε := ε) (A := A)
      (annularContractedUpperRetainedToUpper p))

/-- Contracted form of the masked prefix--future digit decomposition. -/
theorem
    annularContractedUpperRetained_maskedEvent_eq_prefix_inter_futureDigit
    {ε A eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    annularUpperRetainedMaskedApproximationDigitEvent
        ε A N p.1 (mode p.1) (hmode p.1)
        (annularContractedUpperRetainedTimes p) =
      annularUpperRetainedPrefixApproximationEvent ε A
          (annularContractedUpperRetainedToUpper p) ∩
        annularUpperRetainedFutureDigitTupleEvent ε A
          (annularContractedUpperRetainedToUpper p) := by
  simpa only [annularContractedUpperRetainedTimes_embedding] using!
    (annularUpperRetained_maskedEvent_eq_prefix_inter_futureDigit
      (ε := ε) (A := A) hgrid htime
      (annularContractedUpperRetainedToUpper p) hN hW)

/-- Every factor selected by a nonzero literal prefix product carries its
own marked event. -/
theorem gaussPrefixMarkedEvent_of_mixedPrefixCharacter_ne_zero
    {ι : Type*} [Fintype ι]
    {N : ℕ} {B : ι → Set (ℝ × ℝ × ℝ)} {k : ι → ℕ}
    {h : ∀ i, Fin (k i) → ℤ}
    {F : GaussPrefixMixedDepthTuple N k} {m : ℕ} {x : ℝ}
    (hne :
      gaussPrefixMarkedMixedPrefixCharacter N B k h F m x ≠ 0)
    (z : GaussPrefixMixedOccurrence k)
    (hz : (F z.1 z.2 : ℕ) ≤ m) :
    x ∈ gaussPrefixMarkedEvent N (B z.1) (F z.1 z.2) := by
  have hzFactorNe :
      gaussPrefixMarkedDepthCharacter N (B z.1) (F z.1 z.2)
          (h z.1 z.2) x ≠ 0 := by
    intro hzZero
    apply hne
    unfold gaussPrefixMarkedMixedPrefixCharacter
    apply Finset.prod_eq_zero
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩
    · exact hzZero
  by_contra hzNot
  apply hzFactorNe
  unfold gaussPrefixMarkedDepthCharacter
  rw [if_neg hzNot]

/-- If the live delayed prefix character is nonzero, then all exact
oriented prefix windows occur.  This implication is independent of the
future block: it is extracted coordinate by coordinate from the literal
prefix product. -/
theorem
    annularContractedUpperRetained_prefixCharacter_ne_zero_implies_prefixEvent
    {ε A eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hne :
      gaussPrefixMarkedMixedPrefixCharacter N
          (fun i ↦ compactValueMarkedRegion
            (activeAnnularOccurrenceSignedLower k ε A i)
            (activeAnnularOccurrenceSignedUpper k ε A i))
          k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1
          (annularContractedUpperRetainedDelayedDepth p) x ≠ 0) :
    x ∈ annularUpperRetainedPrefixApproximationEvent ε A
      (annularContractedUpperRetainedToUpper p) := by
  rw [mem_annularUpperRetainedPrefixApproximationEvent_iff
    (annularContractedUpperRetainedToUpper p) x]
  intro j hj
  change
    x ∈ gaussApproximationWindow
      (Real.log (N : ℝ))
      (annularContractedUpperRetainedTimes p j)
      (gaussPrescribedParityOrientedLower
        (flattenedAnnularParity p.1)
        (flattenedAnnularSignedLower ε A p.1)
        (flattenedAnnularSignedUpper ε A p.1) j)
      (gaussPrescribedParityOrientedUpper
        (flattenedAnnularParity p.1)
        (flattenedAnnularSignedLower ε A p.1)
        (flattenedAnnularSignedUpper ε A p.1) j)
  let z : GaussPrefixMixedOccurrence k := p.1 j
  have htime :
      ((annularContractedUpperRetainedRealization p).1 z.1 z.2 : ℕ) =
        annularContractedUpperRetainedTimes p j := by
    have hjtime :=
      congrFun (annularContractedUpperRetainedRealization_times p) j
    simpa only [fixedOrderMixedTimes, z] using! hjtime
  have hzDepth :
      ((annularContractedUpperRetainedRealization p).1 z.1 z.2 : ℕ) ≤
        annularContractedUpperRetainedDelayedDepth p := by
    rw [htime]
    exact hj.trans <| by
      unfold annularContractedUpperRetainedDelayedDepth
        annularUpperRetainedDelayedSplitDepth
      exact Nat.le_add_right _ _
  have hzMarked :
      x ∈ gaussPrefixMarkedEvent N
        (compactValueMarkedRegion
          (activeAnnularOccurrenceSignedLower k ε A z.1)
          (activeAnnularOccurrenceSignedUpper k ε A z.1))
        ((annularContractedUpperRetainedRealization p).1 z.1 z.2) := by
    exact gaussPrefixMarkedEvent_of_mixedPrefixCharacter_ne_zero
      hne z hzDepth
  have hdata := selectedGaussPrefixWord_data_of_mem hzMarked
  have hactive : 0 < k z.1 := by
    have hzlt := z.2.isLt
    omega
  have hvalue :
      gaussSignedScaledApproximationCoordinate
          (Real.log (N : ℝ))
          ((annularContractedUpperRetainedRealization p).1
            z.1 z.2 : ℕ) x ∈
        Icc (flattenedAnnularSignedLower ε A p.1 j)
          (flattenedAnnularSignedUpper ε A p.1 j) := by
    have hv := hdata.2.2.2.2.1
    change
      (gaussPrefixMarkedPoint N
        ((annularContractedUpperRetainedRealization p).1
          z.1 z.2 : ℕ)
        (selectedGaussPrefixWord
          ((annularContractedUpperRetainedRealization p).1
            z.1 z.2 : ℕ) x) x).2.1 ∈
        Icc (activeAnnularOccurrenceSignedLower k ε A z.1)
          (activeAnnularOccurrenceSignedUpper k ε A z.1) at hv
    rw [activeAnnularOccurrenceSignedLower_of_pos hactive,
      activeAnnularOccurrenceSignedUpper_of_pos hactive] at hv
    simpa only [z,
      gaussPrefixMarkedPoint_value_eq_signedScaledApproximation] using! hv
  have hsigned :
      x ∈ gaussSignedApproximationWindow
        (Real.log (N : ℝ))
        (annularContractedUpperRetainedTimes p j)
        (flattenedAnnularSignedLower ε A p.1 j)
        (flattenedAnnularSignedUpper ε A p.1 j) := by
    refine ⟨⟨hxUnit.1, hxUnit.2.le⟩, ?_⟩
    simpa only [← htime] using! hvalue
  rw [gaussSignedApproximationWindow_eq_oriented] at hsigned
  have hlower' :
      gaussParityOrientedLower
          (annularContractedUpperRetainedTimes p j)
          (flattenedAnnularSignedLower ε A p.1 j)
          (flattenedAnnularSignedUpper ε A p.1 j) =
        gaussPrescribedParityOrientedLower
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1) j := by
    apply gaussParityOrientedLower_eq_of_mod_two_eq
    rw [Nat.mod_eq_of_lt (flattenedAnnularParity p.1 j).isLt]
    exact annularContractedUpperRetainedTimes_parity p j
  have hupper' :
      gaussParityOrientedUpper
          (annularContractedUpperRetainedTimes p j)
          (flattenedAnnularSignedLower ε A p.1 j)
          (flattenedAnnularSignedUpper ε A p.1 j) =
        gaussPrescribedParityOrientedUpper
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1) j := by
    apply gaussParityOrientedUpper_eq_of_mod_two_eq
    rw [Nat.mod_eq_of_lt (flattenedAnnularParity p.1 j).isLt]
    exact annularContractedUpperRetainedTimes_parity p j
  simpa only [hlower', hupper'] using! hsigned

/-! ## Pointwise localized replacement -/

/-- On a globally denominator-good point, the literal future marked block
may be replaced by the future digit block at the cost of the complete
exact/masked symmetric difference.  The prefix character and the prefix
exact event remain present throughout. -/
theorem
    norm_annularContractedUpperRetained_prefixGoodMixedIntegrand_sub_liveDigit_le
    {ε A eta rho : ℝ} {N grid : ℕ}
    (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxPrefixGood :
      x ∈ gaussDenominatorPrefixGoodEvent
        (annularContractedUpperRetainedDelayedDepth p)
        (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho))
    (hfullEq :
      gaussMovingSignedMarkedTupleIntegrand
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1)
          (mode p.1)
          (annularContractedUpperRetainedTimes p) x =
        gaussPrefixMarkedMixedTupleCharacter N
          (fun i ↦ compactValueMarkedRegion
            (activeAnnularOccurrenceSignedLower k ε A i)
            (activeAnnularOccurrenceSignedUpper k ε A i))
          k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1 x) :
    ‖(gaussDenominatorPrefixGoodEvent
          (annularContractedUpperRetainedDelayedDepth p)
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho)).indicator
        (gaussPrefixMarkedMixedTupleCharacter N
          (fun i ↦ compactValueMarkedRegion
            (activeAnnularOccurrenceSignedLower k ε A i)
            (activeAnnularOccurrenceSignedUpper k ε A i))
          k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1) x -
      (gaussDenominatorPrefixGoodEvent
          (annularContractedUpperRetainedDelayedDepth p)
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho)).indicator
        (fun y ↦
          gaussPrefixMarkedMixedPrefixCharacter N
              (fun i ↦ compactValueMarkedRegion
                (activeAnnularOccurrenceSignedLower k ε A i)
                (activeAnnularOccurrenceSignedUpper k ε A i))
              k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedDelayedDepth p) y *
            annularContractedUpperRetainedFutureDigitBlock ε A p y) x‖ ≤
      (gaussHeterogeneousApproximationTupleEvent
              (Real.log (N : ℝ))
              (gaussPrescribedParityOrientedLower
                (flattenedAnnularParity p.1)
                (flattenedAnnularSignedLower ε A p.1)
                (flattenedAnnularSignedUpper ε A p.1))
              (gaussPrescribedParityOrientedUpper
                (flattenedAnnularParity p.1)
                (flattenedAnnularSignedLower ε A p.1)
                (flattenedAnnularSignedUpper ε A p.1))
              (annularContractedUpperRetainedTimes p) ∆
            annularUpperRetainedMaskedApproximationDigitEvent
              ε A N p.1 (mode p.1) (hmode p.1)
              (annularContractedUpperRetainedTimes p)).indicator
        (fun _x ↦ (1 : ℝ)) x := by
  let B : AnnularGridIndex grid → Set (ℝ × ℝ × ℝ) := fun i ↦
    compactValueMarkedRegion
      (activeAnnularOccurrenceSignedLower k ε A i)
      (activeAnnularOccurrenceSignedUpper k ε A i)
  let F : GaussPrefixMixedDepthTuple N k :=
    (annularContractedUpperRetainedRealization p).1
  let b : ℕ := annularContractedUpperRetainedDelayedDepth p
  let prefChar : ℂ :=
    gaussPrefixMarkedMixedPrefixCharacter N B k
      (unflattenedAnnularFourierMode p.1 (mode p.1)) F b x
  let futureMarked : Set ℝ :=
    gaussPrefixMarkedMixedFutureEvent N B k F b
  let futureDigit : Set ℝ :=
    annularUpperRetainedFutureDigitTupleEvent ε A
      (annularContractedUpperRetainedToUpper p)
  let exactEvent : Set ℝ :=
    gaussHeterogeneousApproximationTupleEvent
      (Real.log (N : ℝ))
      (gaussPrescribedParityOrientedLower
        (flattenedAnnularParity p.1)
        (flattenedAnnularSignedLower ε A p.1)
        (flattenedAnnularSignedUpper ε A p.1))
      (gaussPrescribedParityOrientedUpper
        (flattenedAnnularParity p.1)
        (flattenedAnnularSignedLower ε A p.1)
        (flattenedAnnularSignedUpper ε A p.1))
      (annularContractedUpperRetainedTimes p)
  let digitEvent : Set ℝ :=
    annularUpperRetainedMaskedApproximationDigitEvent
      ε A N p.1 (mode p.1) (hmode p.1)
      (annularContractedUpperRetainedTimes p)
  have hsplit :
      gaussPrefixMarkedMixedTupleCharacter N B k
          (unflattenedAnnularFourierMode p.1 (mode p.1)) F x =
        prefChar *
          futureMarked.indicator (fun _ ↦ (1 : ℂ)) x := by
    apply gaussPrefixMarkedMixedTupleCharacter_eq_prefix_mul_futureIndicator
    intro z hz
    have hzSplit :
        annularUpperRetainedSplitDepth
            (annularContractedUpperRetainedToUpper p) <
          ((annularContractedUpperRetainedRealization p).1
            z.1 z.2 : ℕ) := by
      exact
        (annularUpperRetained_labeled_after_delayed_iff_after_split
          hgrid htime (annularContractedUpperRetainedToUpper p)
          hN hW z).mp <| by
            simpa only [F, b,
              annularContractedUpperRetainedDelayedDepth_embedding] using! hz
    let j : Fin (MixedOccurrenceCount k) := p.1.symm z
    have htimeEq :
        annularContractedUpperRetainedTimes p j =
          ((annularContractedUpperRetainedRealization p).1
            z.1 z.2 : ℕ) := by
      have htimes :=
        congrFun (annularContractedUpperRetainedRealization_times p) j
      change
        ((annularContractedUpperRetainedRealization p).1
            (p.1 j).1 (p.1 j).2 : ℕ) =
          annularContractedUpperRetainedTimes p j at htimes
      have hej : p.1 j = z := p.1.apply_symm_apply z
      rw [hej] at htimes
      exact htimes.symm
    have hgap :=
      (annularUpperRetainedRealization_gap_package
        hgrid htime (annularContractedUpperRetainedToUpper p)
        hN hW).2.2 j
    have hj : mode p.1 j = 0 := by
      apply hgap
      simpa only [annularContractedUpperRetainedTimes_embedding,
        htimeEq] using! hzSplit
    simpa only [unflattenedAnnularFourierMode, j,
      p.1.symm_apply_apply] using! hj
  have hfutureDigit :
      annularContractedUpperRetainedFutureDigitBlock ε A p x =
        futureDigit.indicator (fun _ ↦ (1 : ℂ)) x := by
    simpa only [annularContractedUpperRetainedFutureDigitBlock,
      annularContractedUpperRetainedUpperTag, futureDigit] using!
      (annularUpperRetainedFutureDigitBlock_eq_eventIndicator
        (ε := ε) (A := A)
        (annularContractedUpperRetainedToUpper p) x)
  have hmixedIffExact :
      x ∈ mixedTupleEvent
          (fun i ↦ gaussPrefixMarkedEvent N (B i)) F ↔
        x ∈ exactEvent := by
    have hnorm := congrArg norm hfullEq
    rw [norm_gaussMovingSignedMarkedTupleIntegrand,
      norm_gaussPrefixMarkedMixedTupleCharacter_eq_indicator] at hnorm
    have hsigned :=
      annularContractedUpperRetained_signedTupleEvent_eq_exactTupleEvent
        (ε := ε) (A := A) p
    rw [hsigned] at hnorm
    change
      (exactEvent.indicator (fun _x ↦ (1 : ℝ)) x) =
        (mixedTupleEvent
          (fun i ↦ gaussPrefixMarkedEvent N (B i)) F).indicator
            (fun _x ↦ (1 : ℝ)) x at hnorm
    constructor
    · intro hmixed
      by_contra hexact
      rw [Set.indicator_of_notMem hexact,
        Set.indicator_of_mem hmixed] at hnorm
      norm_num at hnorm
    · intro hexact
      by_contra hmixed
      rw [Set.indicator_of_mem hexact,
        Set.indicator_of_notMem hmixed] at hnorm
      norm_num at hnorm
  rw [Set.indicator_of_mem hxPrefixGood,
    Set.indicator_of_mem hxPrefixGood]
  change
    ‖gaussPrefixMarkedMixedTupleCharacter N B k
          (unflattenedAnnularFourierMode p.1 (mode p.1)) F x -
        prefChar *
          annularContractedUpperRetainedFutureDigitBlock ε A p x‖ ≤
      (exactEvent ∆ digitEvent).indicator (fun _x ↦ (1 : ℝ)) x
  rw [hsplit, hfutureDigit]
  by_cases hprefixZero : prefChar = 0
  · simpa [hprefixZero] using!
      (Set.indicator_nonneg
        (s := exactEvent ∆ digitEvent) (fun _x ↦ by norm_num) x)
  have hprefixExact :
      x ∈ annularUpperRetainedPrefixApproximationEvent ε A
        (annularContractedUpperRetainedToUpper p) := by
    apply
      annularContractedUpperRetained_prefixCharacter_ne_zero_implies_prefixEvent
        (p := p) hxUnit
    simpa only [B, F, b, prefChar] using! hprefixZero
  have hprefixMarked :
      ∀ z : GaussPrefixMixedOccurrence k,
        (F z.1 z.2 : ℕ) ≤ b →
          x ∈ gaussPrefixMarkedEvent N (B z.1) (F z.1 z.2) := by
    intro z hz
    apply gaussPrefixMarkedEvent_of_mixedPrefixCharacter_ne_zero
      (z := z) (hz := hz)
    simpa only [prefChar] using! hprefixZero
  have hfutureIff :
      x ∈ futureMarked ↔
        x ∈ annularUpperRetainedFutureApproximationEvent ε A
          (annularContractedUpperRetainedToUpper p) := by
    constructor
    · intro hfuture
      have hmixed :
          x ∈ mixedTupleEvent
            (fun i ↦ gaussPrefixMarkedEvent N (B i)) F := by
        apply Set.mem_iInter.mpr
        intro i
        apply Set.mem_iInter.mpr
        intro j
        let z : GaussPrefixMixedOccurrence k := ⟨i, j⟩
        by_cases hz : (F z.1 z.2 : ℕ) ≤ b
        · exact hprefixMarked z hz
        · have hzDelayed : b < (F z.1 z.2 : ℕ) :=
            Nat.lt_of_not_ge hz
          exact hfuture z hzDelayed
      have hexact := hmixedIffExact.mp hmixed
      rw [show exactEvent =
          annularUpperRetainedPrefixApproximationEvent ε A
              (annularContractedUpperRetainedToUpper p) ∩
            annularUpperRetainedFutureApproximationEvent ε A
              (annularContractedUpperRetainedToUpper p) by
        simpa only [exactEvent] using!
          (annularContractedUpperRetained_exactTupleEvent_eq_prefix_inter_future
            (ε := ε) (A := A) p)] at hexact
      exact hexact.2
    · intro hfuture
      have hexact : x ∈ exactEvent := by
        rw [show exactEvent =
            annularUpperRetainedPrefixApproximationEvent ε A
                (annularContractedUpperRetainedToUpper p) ∩
              annularUpperRetainedFutureApproximationEvent ε A
                (annularContractedUpperRetainedToUpper p) by
          simpa only [exactEvent] using!
            (annularContractedUpperRetained_exactTupleEvent_eq_prefix_inter_future
              (ε := ε) (A := A) p)]
        exact ⟨hprefixExact, hfuture⟩
      have hmixed := hmixedIffExact.mpr hexact
      intro z hz
      exact Set.mem_iInter.mp
        (Set.mem_iInter.mp hmixed z.1) z.2
  have hexactIff :
      x ∈ exactEvent ↔ x ∈ futureMarked := by
    rw [show exactEvent =
        annularUpperRetainedPrefixApproximationEvent ε A
            (annularContractedUpperRetainedToUpper p) ∩
          annularUpperRetainedFutureApproximationEvent ε A
            (annularContractedUpperRetainedToUpper p) by
      simpa only [exactEvent] using!
        (annularContractedUpperRetained_exactTupleEvent_eq_prefix_inter_future
          (ε := ε) (A := A) p)]
    simp only [Set.mem_inter_iff, hprefixExact, true_and]
    exact hfutureIff.symm
  have hdigitIff :
      x ∈ digitEvent ↔ x ∈ futureDigit := by
    rw [show digitEvent =
        annularUpperRetainedPrefixApproximationEvent ε A
            (annularContractedUpperRetainedToUpper p) ∩
          annularUpperRetainedFutureDigitTupleEvent ε A
            (annularContractedUpperRetainedToUpper p) by
      simpa only [digitEvent] using!
        (annularContractedUpperRetained_maskedEvent_eq_prefix_inter_futureDigit
          (ε := ε) (A := A) hgrid htime p hN hW)]
    simp only [Set.mem_inter_iff, hprefixExact, true_and, futureDigit]
  have hprefixNorm : ‖prefChar‖ ≤ 1 := by
    simpa only [prefChar] using!
      norm_gaussPrefixMarkedMixedPrefixCharacter_le_one
        N B k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        F b x
  by_cases hmarked : x ∈ futureMarked
  · by_cases hdigit : x ∈ futureDigit
    · rw [Set.indicator_of_mem hmarked, Set.indicator_of_mem hdigit]
      simpa using!
        (Set.indicator_nonneg
          (s := exactEvent ∆ digitEvent) (fun _x ↦ by norm_num) x)
    · have hexact : x ∈ exactEvent := hexactIff.mpr hmarked
      have hnotDigitEvent : x ∉ digitEvent :=
        fun hx ↦ hdigit (hdigitIff.mp hx)
      have hsymm : x ∈ exactEvent ∆ digitEvent :=
        Or.inl ⟨hexact, hnotDigitEvent⟩
      rw [Set.indicator_of_mem hmarked,
        Set.indicator_of_notMem hdigit,
        Set.indicator_of_mem hsymm]
      simpa using! hprefixNorm
  · by_cases hdigit : x ∈ futureDigit
    · have hnotExact : x ∉ exactEvent :=
        fun hx ↦ hmarked (hexactIff.mp hx)
      have hdigitEvent : x ∈ digitEvent := hdigitIff.mpr hdigit
      have hsymm : x ∈ exactEvent ∆ digitEvent :=
        Or.inr ⟨hdigitEvent, hnotExact⟩
      rw [Set.indicator_of_notMem hmarked,
        Set.indicator_of_mem hdigit,
        Set.indicator_of_mem hsymm]
      simpa using! hprefixNorm
    · rw [Set.indicator_of_notMem hmarked,
        Set.indicator_of_notMem hdigit]
      simpa using!
        (Set.indicator_nonneg
          (s := exactEvent ∆ digitEvent) (fun _x ↦ by norm_num) x)

/-! ## Finite-family localized comparison -/

/-- Finite-`N` aggregate comparison.  The first term is the complete
exact/masked replacement error.  On the denominator-bad set the live digit
integrand is supported by the union of the homogeneous exact window and
that same replacement error; this is why no future denominator condition
is silently discarded. -/
theorem
    norm_annularContractedUpperRetainedPrefixGoodMixedSum_sub_liveDigitJointSum_le
    {ε A eta rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {N grid : ℕ} (hgrid : 0 < grid) (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hmargin :
      upperGoodTransferDenominatorTolerance eta rho *
          (annularDepthAmbientSize N : ℝ) ≤
        eta * Real.log (N : ℝ)) :
    ‖annularContractedUpperRetainedPrefixGoodMixedSum
          ε A eta rho N k hr mode hmode -
        annularContractedUpperRetainedLiveDigitJointSum
          ε A eta rho N k hr mode hmode‖ ≤
      (∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        uniform01Measure.real
          (gaussHeterogeneousApproximationTupleEvent
                (Real.log (N : ℝ))
                (gaussPrescribedParityOrientedLower
                  (flattenedAnnularParity p.1)
                  (flattenedAnnularSignedLower ε A p.1)
                  (flattenedAnnularSignedUpper ε A p.1))
                (gaussPrescribedParityOrientedUpper
                  (flattenedAnnularParity p.1)
                  (flattenedAnnularSignedLower ε A p.1)
                  (flattenedAnnularSignedUpper ε A p.1))
                (annularContractedUpperRetainedTimes p) ∆
              annularUpperRetainedMaskedApproximationDigitEvent
                ε A N p.1 (mode p.1) (hmode p.1)
                (annularContractedUpperRetainedTimes p))) +
        ∫ x in
            (gaussDenominatorLinearGoodEvent 1
              (annularDepthAmbientSize N)
              (upperGoodTransferDenominatorTolerance eta rho))ᶜ,
          2 * ∑ p : AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode,
            ((orderedEventIntersection
                (List.ofFn fun j ↦
                  gaussApproximationWindow (Real.log (N : ℝ))
                    (annularContractedUpperRetainedTimes p j) ε A)) ∪
              (gaussHeterogeneousApproximationTupleEvent
                    (Real.log (N : ℝ))
                    (gaussPrescribedParityOrientedLower
                      (flattenedAnnularParity p.1)
                      (flattenedAnnularSignedLower ε A p.1)
                      (flattenedAnnularSignedUpper ε A p.1))
                    (gaussPrescribedParityOrientedUpper
                      (flattenedAnnularParity p.1)
                      (flattenedAnnularSignedLower ε A p.1)
                      (flattenedAnnularSignedUpper ε A p.1))
                    (annularContractedUpperRetainedTimes p) ∆
                  annularUpperRetainedMaskedApproximationDigitEvent
                    ε A N p.1 (mode p.1) (hmode p.1)
                    (annularContractedUpperRetainedTimes p))).indicator
              (fun _x ↦ (1 : ℝ)) x
          ∂uniform01Measure := by
  classical
  let T :=
    AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode
  let good : Set ℝ :=
    gaussDenominatorLinearGoodEvent 1
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  let P : T → Set ℝ := fun p ↦
    gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  let B : AnnularGridIndex grid → Set (ℝ × ℝ × ℝ) := fun i ↦
    compactValueMarkedRegion
      (activeAnnularOccurrenceSignedLower k ε A i)
      (activeAnnularOccurrenceSignedUpper k ε A i)
  let exactEvent : T → Set ℝ := fun p ↦
    gaussHeterogeneousApproximationTupleEvent
      (Real.log (N : ℝ))
      (gaussPrescribedParityOrientedLower
        (flattenedAnnularParity p.1)
        (flattenedAnnularSignedLower ε A p.1)
        (flattenedAnnularSignedUpper ε A p.1))
      (gaussPrescribedParityOrientedUpper
        (flattenedAnnularParity p.1)
        (flattenedAnnularSignedLower ε A p.1)
        (flattenedAnnularSignedUpper ε A p.1))
      (annularContractedUpperRetainedTimes p)
  let digitEvent : T → Set ℝ := fun p ↦
    annularUpperRetainedMaskedApproximationDigitEvent
      ε A N p.1 (mode p.1) (hmode p.1)
      (annularContractedUpperRetainedTimes p)
  let replacementError : T → Set ℝ := fun p ↦
    exactEvent p ∆ digitEvent p
  let homogeneous : T → Set ℝ := fun p ↦
    orderedEventIntersection
      (List.ofFn fun j ↦
        gaussApproximationWindow (Real.log (N : ℝ))
          (annularContractedUpperRetainedTimes p j) ε A)
  let envelope : T → Set ℝ := fun p ↦
    homogeneous p ∪ replacementError p
  let f : T → ℝ → ℂ := fun p ↦
    (P p).indicator
      (gaussPrefixMarkedMixedTupleCharacter N B k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedUpperRetainedRealization p).1)
  let g : T → ℝ → ℂ := fun p ↦
    (P p).indicator fun x ↦
      gaussPrefixMarkedMixedPrefixCharacter N B k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1
          (annularContractedUpperRetainedDelayedDepth p) x *
        annularContractedUpperRetainedFutureDigitBlock ε A p x
  have hgoodMeas : MeasurableSet good :=
    measurableSet_gaussDenominatorLinearGoodEvent
      1 (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho)
  have herrorMeas : ∀ p ∈ (Finset.univ : Finset T),
      MeasurableSet (replacementError p) := by
    intro p _hp
    exact
      (measurableSet_gaussHeterogeneousApproximationTupleEvent
        (Real.log (N : ℝ))
        (gaussPrescribedParityOrientedLower
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1))
        (gaussPrescribedParityOrientedUpper
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1))
        (annularContractedUpperRetainedTimes p)).symmDiff
        (by
          unfold digitEvent
          unfold annularUpperRetainedMaskedApproximationDigitEvent
          apply measurableSet_maskedOrderedEventIntersection
          · intro j
            exact measurableSet_gaussApproximationWindow _ _ _ _
          · intro j
            exact measurableSet_gaussDigitWindowAt _ _ _ _)
  have hhomogeneousMeas : ∀ p ∈ (Finset.univ : Finset T),
      MeasurableSet (homogeneous p) := by
    intro p _hp
    apply measurableSet_orderedEventIntersection
    intro S hS
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hS
    exact measurableSet_gaussApproximationWindow _ _ _ _
  have henvelopeMeas : ∀ p ∈ (Finset.univ : Finset T),
      MeasurableSet (envelope p) := by
    intro p hp
    exact (hhomogeneousMeas p hp).union (herrorMeas p hp)
  have hfInt : ∀ p ∈ (Finset.univ : Finset T),
      Integrable (f p) uniform01Measure := by
    intro p _hp
    exact
      (integrable_gaussPrefixMarkedMixedTupleCharacter N
        (fun i ↦ measurableSet_compactValueMarkedRegion
          (activeAnnularOccurrenceSignedLower k ε A i)
          (activeAnnularOccurrenceSignedUpper k ε A i))
        k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedUpperRetainedRealization p).1
        uniform01Measure).indicator
          (measurableSet_gaussDenominatorPrefixGoodEvent
            (annularContractedUpperRetainedDelayedDepth p)
            (annularDepthAmbientSize N)
            (upperGoodTransferDenominatorTolerance eta rho))
  have hgInt : ∀ p ∈ (Finset.univ : Finset T),
      Integrable (g p) uniform01Measure := by
    intro p _hp
    have hprefixMeas :
        Measurable
          (gaussPrefixMarkedMixedPrefixCharacter N B k
            (unflattenedAnnularFourierMode p.1 (mode p.1))
            (annularContractedUpperRetainedRealization p).1
            (annularContractedUpperRetainedDelayedDepth p)) := by
      unfold gaussPrefixMarkedMixedPrefixCharacter
      apply Finset.measurable_fun_prod
      intro z _hz
      exact measurable_gaussPrefixMarkedDepthCharacter N
        ((annularContractedUpperRetainedRealization p).1 z.1 z.2)
        (measurableSet_compactValueMarkedRegion
          (activeAnnularOccurrenceSignedLower k ε A z.1)
          (activeAnnularOccurrenceSignedUpper k ε A z.1))
        (unflattenedAnnularFourierMode p.1 (mode p.1) z.1 z.2)
    have hfutureMeas :
        Measurable
          (annularContractedUpperRetainedFutureDigitBlock ε A p) := by
      have heq :
          annularContractedUpperRetainedFutureDigitBlock ε A p =
            (annularUpperRetainedFutureDigitTupleEvent ε A
              (annularContractedUpperRetainedToUpper p)).indicator
                (fun _ ↦ (1 : ℂ)) := by
        funext x
        exact annularUpperRetainedFutureDigitBlock_eq_eventIndicator
          (ε := ε) (A := A)
          (annularContractedUpperRetainedToUpper p) x
      rw [heq]
      exact Measurable.ite
        (measurableSet_annularUpperRetainedFutureDigitTupleEvent
          (ε := ε) (A := A)
          (annularContractedUpperRetainedToUpper p))
        measurable_const measurable_const
    apply Integrable.of_bound
      ((hprefixMeas.mul hfutureMeas).indicator
        (measurableSet_gaussDenominatorPrefixGoodEvent
          (annularContractedUpperRetainedDelayedDepth p)
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho))).aestronglyMeasurable
      1
    filter_upwards with x
    by_cases hxP :
        x ∈ gaussDenominatorPrefixGoodEvent
          (annularContractedUpperRetainedDelayedDepth p)
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho)
    · rw [Set.indicator_of_mem hxP, Pi.mul_apply, norm_mul]
      have hpref :=
        norm_gaussPrefixMarkedMixedPrefixCharacter_le_one
          N B k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1
          (annularContractedUpperRetainedDelayedDepth p) x
      have hfuture :
          ‖annularContractedUpperRetainedFutureDigitBlock ε A p x‖ ≤ 1 := by
        rw [annularContractedUpperRetainedFutureDigitBlock,
          annularUpperRetainedFutureDigitBlock_eq_eventIndicator]
        by_cases hx :
            x ∈ annularUpperRetainedFutureDigitTupleEvent ε A
              (annularContractedUpperRetainedToUpper p) <;>
          simp [Set.indicator, hx]
      nlinarith [norm_nonneg
        (gaussPrefixMarkedMixedPrefixCharacter N B k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1
          (annularContractedUpperRetainedDelayedDepth p) x)]
    · rw [Set.indicator_of_notMem hxP, norm_zero]
      norm_num
  have hclose :
      ∀ᵐ x ∂uniform01Measure, x ∈ good →
        ∀ p ∈ (Finset.univ : Finset T),
          ‖f p x - g p x‖ ≤
            (replacementError p).indicator
              (fun _x ↦ (1 : ℝ)) x := by
    have hall :
        ∀ᵐ x ∂uniform01Measure,
          ∀ p : T, x ∈ good →
            ‖f p x - g p x‖ ≤
              (replacementError p).indicator
                (fun _x ↦ (1 : ℝ)) x := by
      apply Filter.eventually_all.mpr
      intro p
      have hbridge :=
        ae_annularContractedUpperRetained_moving_eq_prefixGoodMixed_on_globalGood
          hε hεA hgrid hN hW k hr htime hsigned mode hmode
          hsmall hmargin p
      have hprefix :
          good ≤ᵐ[uniform01Measure] P p := by
        apply gaussDenominatorLinearGoodEvent_ae_subset_prefixGoodEvent
        simpa only [one_mul] using!
          (annularContractedUpperRetainedDelayedDepth_lt_ambient
            hgrid htime p (by omega) hW).le
      filter_upwards [ae_nonterminating_uniform01, hbridge, hprefix] with
          x hxUnit hxBridge hxPrefix hxGood
      have hxP : x ∈ P p := hxPrefix hxGood
      have hfullEq :
          gaussMovingSignedMarkedTupleIntegrand
              N (Real.log (N : ℝ))
              (flattenedAnnularSignedLower ε A p.1)
              (flattenedAnnularSignedUpper ε A p.1)
              (mode p.1)
              (annularContractedUpperRetainedTimes p) x =
            gaussPrefixMarkedMixedTupleCharacter N B k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1 x := by
        simpa only [P, B, Set.indicator_of_mem hxP] using! hxBridge hxGood
      simpa only [f, g, P, B, replacementError, exactEvent, digitEvent]
        using!
          norm_annularContractedUpperRetained_prefixGoodMixedIntegrand_sub_liveDigit_le
            hgrid htime p (by omega) hW hxUnit.1 hxP hfullEq
    filter_upwards [hall] with x hx hxGood p _hp
    exact hx p hxGood
  have hbound :
      ∀ᵐ x ∂uniform01Measure,
        ∀ p ∈ (Finset.univ : Finset T),
          ‖f p x‖ ≤
              (envelope p).indicator (fun _x ↦ (1 : ℝ)) x ∧
            ‖g p x‖ ≤
              (envelope p).indicator (fun _x ↦ (1 : ℝ)) x := by
    filter_upwards [ae_nonterminating_uniform01] with x hxUnit
    intro p _hp
    have hexactSubsetHomogeneous :
        exactEvent p ⊆ homogeneous p := by
      intro y hy
      have hsignedEvent :
          y ∈ gaussSignedApproximationTupleEvent
            (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A p.1)
            (flattenedAnnularSignedUpper ε A p.1)
            (annularContractedUpperRetainedTimes p) := by
        rw [
          annularContractedUpperRetained_signedTupleEvent_eq_exactTupleEvent
            (ε := ε) (A := A) p]
        exact hy
      exact
        annularContractedUpperRetained_signedEvent_subset_windowEvent
          hεA hgrid hsigned p hsignedEvent
    constructor
    · dsimp only [f]
      by_cases hxP : x ∈ P p
      · rw [Set.indicator_of_mem hxP]
        rw [norm_gaussPrefixMarkedMixedTupleCharacter_eq_indicator]
        by_cases hxMixed :
            x ∈ mixedTupleEvent
              (fun i ↦ gaussPrefixMarkedEvent N (B i))
              (annularContractedUpperRetainedRealization p).1
        · have hxHomogeneous : x ∈ homogeneous p := by
            apply
              annularContractedUpperRetained_mixedEvent_subset_windowEvent_of_mem_Ioc
                hεA hgrid hsigned p
            · exact ⟨hxUnit.1.1, hxUnit.1.2.le⟩
            · simpa only [B] using! hxMixed
          have hxEnvelope : x ∈ envelope p := by
            exact Or.inl hxHomogeneous
          rw [Set.indicator_of_mem hxMixed,
            Set.indicator_of_mem hxEnvelope]
        · rw [Set.indicator_of_notMem hxMixed]
          exact Set.indicator_nonneg (fun _x ↦ by norm_num) x
      · rw [Set.indicator_of_notMem hxP, norm_zero]
        exact Set.indicator_nonneg (fun _x ↦ by norm_num) x
    · dsimp only [g]
      by_cases hxP : x ∈ P p
      · rw [Set.indicator_of_mem hxP, norm_mul]
        let pref : ℂ :=
          gaussPrefixMarkedMixedPrefixCharacter N B k
            (unflattenedAnnularFourierMode p.1 (mode p.1))
            (annularContractedUpperRetainedRealization p).1
            (annularContractedUpperRetainedDelayedDepth p) x
        by_cases hprefZero : pref = 0
        · rw [show
            gaussPrefixMarkedMixedPrefixCharacter N B k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedDelayedDepth p) x = 0 by
            simpa only [pref] using! hprefZero]
          simp only [norm_zero, zero_mul]
          exact Set.indicator_nonneg (fun _x ↦ by norm_num) x
        · have hxPrefix :
              x ∈ annularUpperRetainedPrefixApproximationEvent ε A
                (annularContractedUpperRetainedToUpper p) := by
            apply
              annularContractedUpperRetained_prefixCharacter_ne_zero_implies_prefixEvent
                (p := p) hxUnit.1
            simpa only [B, pref] using! hprefZero
          by_cases hxFuture :
              x ∈ annularUpperRetainedFutureDigitTupleEvent ε A
                (annularContractedUpperRetainedToUpper p)
          · have hxDigit : x ∈ digitEvent p := by
              rw [show digitEvent p =
                  annularUpperRetainedPrefixApproximationEvent ε A
                      (annularContractedUpperRetainedToUpper p) ∩
                    annularUpperRetainedFutureDigitTupleEvent ε A
                      (annularContractedUpperRetainedToUpper p) by
                simpa only [digitEvent] using!
                  (annularContractedUpperRetained_maskedEvent_eq_prefix_inter_futureDigit
                    (ε := ε) (A := A) hgrid htime p (by omega) hW)]
              exact ⟨hxPrefix, hxFuture⟩
            have hxEnvelope : x ∈ envelope p := by
              by_cases hxExact : x ∈ exactEvent p
              · exact Or.inl (hexactSubsetHomogeneous hxExact)
              · exact Or.inr (Or.inr ⟨hxDigit, hxExact⟩)
            rw [Set.indicator_of_mem hxEnvelope]
            have hprefNorm :
                ‖gaussPrefixMarkedMixedPrefixCharacter N B k
                    (unflattenedAnnularFourierMode p.1 (mode p.1))
                    (annularContractedUpperRetainedRealization p).1
                    (annularContractedUpperRetainedDelayedDepth p) x‖ ≤ 1 :=
              norm_gaussPrefixMarkedMixedPrefixCharacter_le_one
                N B k
                (unflattenedAnnularFourierMode p.1 (mode p.1))
                (annularContractedUpperRetainedRealization p).1
                (annularContractedUpperRetainedDelayedDepth p) x
            have hfutureNorm :
                ‖annularContractedUpperRetainedFutureDigitBlock ε A p x‖ =
                  1 := by
              rw [annularContractedUpperRetainedFutureDigitBlock,
                annularUpperRetainedFutureDigitBlock_eq_eventIndicator,
                Set.indicator_of_mem hxFuture, norm_one]
            rw [hfutureNorm, mul_one]
            exact hprefNorm
          · have hfutureZero :
                annularContractedUpperRetainedFutureDigitBlock ε A p x = 0 := by
              rw [annularContractedUpperRetainedFutureDigitBlock,
                annularUpperRetainedFutureDigitBlock_eq_eventIndicator,
                Set.indicator_of_notMem hxFuture]
            rw [hfutureZero, norm_zero, mul_zero]
            exact Set.indicator_nonneg (fun _x ↦ by norm_num) x
      · rw [Set.indicator_of_notMem hxP, norm_zero]
        exact Set.indicator_nonneg (fun _x ↦ by norm_num) x
  have hcompare :=
    norm_sum_integral_sub_le_error_add_goodCompl_indicatorSum
      uniform01Measure (Finset.univ : Finset T)
      good hgoodMeas replacementError envelope
      herrorMeas henvelopeMeas f g hfInt hgInt hclose hbound
  unfold annularContractedUpperRetainedPrefixGoodMixedSum
    annularContractedUpperRetainedPrefixGoodMixedContribution
    annularContractedUpperRetainedLiveDigitJointSum
    annularContractedUpperRetainedLiveDigitJoint
  rw [← Finset.sum_sub_distrib]
  simpa only [T, good, P, B, exactEvent, digitEvent,
    replacementError, homogeneous, envelope, f, g] using! hcompare

/-! ## Scalar assembly -/

/-- The tagged uniform-Lebesgue mass of the exact/masked replacement
error on the contracted upper family. -/
def annularContractedUpperRetainedTaggedUniformReplacementError
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℝ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    uniform01Measure.real
      (gaussHeterogeneousApproximationTupleEvent
            (Real.log (N : ℝ))
            (gaussPrescribedParityOrientedLower
              (flattenedAnnularParity p.1)
              (flattenedAnnularSignedLower ε A p.1)
              (flattenedAnnularSignedUpper ε A p.1))
            (gaussPrescribedParityOrientedUpper
              (flattenedAnnularParity p.1)
              (flattenedAnnularSignedLower ε A p.1)
              (flattenedAnnularSignedUpper ε A p.1))
            (annularContractedUpperRetainedTimes p) ∆
          annularUpperRetainedMaskedApproximationDigitEvent
            ε A N p.1 (mode p.1) (hmode p.1)
            (annularContractedUpperRetainedTimes p))

/-- Reindex the tagged uniform replacement mass as the nested sum over
chronological orders and contracted time tuples. -/
theorem
    sum_annularContractedUpperRetained_taggedUniformReplacement_eq_nested
    {ε A eta rho : ℝ} {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    (∑ p : AnnularContractedUpperRetainedTaggedTuple
        eta rho N k hr mode hmode,
      uniform01Measure.real
        (gaussHeterogeneousApproximationTupleEvent
              (Real.log (N : ℝ))
              (gaussPrescribedParityOrientedLower
                (flattenedAnnularParity p.1)
                (flattenedAnnularSignedLower ε A p.1)
                (flattenedAnnularSignedUpper ε A p.1))
              (gaussPrescribedParityOrientedUpper
                (flattenedAnnularParity p.1)
                (flattenedAnnularSignedLower ε A p.1)
                (flattenedAnnularSignedUpper ε A p.1))
              (annularContractedUpperRetainedTimes p) ∆
            annularUpperRetainedMaskedApproximationDigitEvent
              ε A N p.1 (mode p.1) (hmode p.1)
              (annularContractedUpperRetainedTimes p))) =
      ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ∑ t ∈
          contractedAnnularCanonicalLaterUpperMidpointTupleFamily
            eta rho N k hr e (mode e) (hmode e),
          uniform01Measure.real
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
                  ε A N e (mode e) (hmode e) t) := by
  classical
  let f := fun
      (e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (p : ↥(contractedAnnularCanonicalLaterUpperMidpointTupleFamily
        eta rho N k hr e (mode e) (hmode e))) ↦
    uniform01Measure.real
      (gaussHeterogeneousApproximationTupleEvent
            (Real.log (N : ℝ))
            (gaussPrescribedParityOrientedLower
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e))
            (gaussPrescribedParityOrientedUpper
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e)) p.1 ∆
          annularUpperRetainedMaskedApproximationDigitEvent
            ε A N e (mode e) (hmode e) p.1)
  change
    (∑ p : Σ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ↥(contractedAnnularCanonicalLaterUpperMidpointTupleFamily
          eta rho N k hr e (mode e) (hmode e)),
      f p.1 p.2) = _
  rw [Fintype.sum_sigma']
  apply Finset.sum_congr rfl
  intro e _he
  rw [← Finset.attach_eq_univ
    (s := contractedAnnularCanonicalLaterUpperMidpointTupleFamily
      eta rho N k hr e (mode e) (hmode e))]
  simp only [f]
  exact Finset.sum_attach
    (contractedAnnularCanonicalLaterUpperMidpointTupleFamily
      eta rho N k hr e (mode e) (hmode e))
    (fun t ↦
      uniform01Measure.real
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
              ε A N e (mode e) (hmode e) t))

/-- The tagged uniform-Lebesgue mass of the complete exact/masked
replacement error tends to zero. -/
theorem
    tendsto_sum_annularContractedUpperRetained_taggedUniformReplacement_zero
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
      (fun N : ℕ ↦
        ∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          uniform01Measure.real
            (gaussHeterogeneousApproximationTupleEvent
                  (Real.log (N : ℝ))
                  (gaussPrescribedParityOrientedLower
                    (flattenedAnnularParity p.1)
                    (flattenedAnnularSignedLower ε A p.1)
                    (flattenedAnnularSignedUpper ε A p.1))
                  (gaussPrescribedParityOrientedUpper
                    (flattenedAnnularParity p.1)
                    (flattenedAnnularSignedLower ε A p.1)
                    (flattenedAnnularSignedUpper ε A p.1))
                  (annularContractedUpperRetainedTimes p) ∆
                annularUpperRetainedMaskedApproximationDigitEvent
                  ε A N p.1 (mode p.1) (hmode p.1)
                  (annularContractedUpperRetainedTimes p)))
      atTop (nhds 0) := by
  let gaussError : ℕ → ℝ := fun N ↦
    aggregateContractedAnnularUpperRetainedJointFutureReplacementError
      ε A eta rho N k hr mode hmode
  have hgauss : Tendsto gaussError atTop (nhds 0) := by
    simpa only [gaussError] using!
      tendsto_contractedAnnularUpperRetained_jointFutureReplacement_zero
        hε hεA eta rho hgrid k hr htime hsigned mode hmode
  have hscaled :
      Tendsto (fun N ↦ (2 * Real.log 2) * gaussError N)
        atTop (nhds 0) := by
    simpa only [mul_zero] using! tendsto_const_nhds.mul hgauss
  refine squeeze_zero'
    (Eventually.of_forall fun N ↦
      Finset.sum_nonneg fun _p _hp ↦ measureReal_nonneg)
    ?_ hscaled
  exact Eventually.of_forall fun N ↦ by
      rw [
        sum_annularContractedUpperRetained_taggedUniformReplacement_eq_nested
          k hr mode hmode]
      unfold gaussError
      unfold
        aggregateContractedAnnularUpperRetainedJointFutureReplacementError
      calc
        (∑ e : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k,
            ∑ t ∈
              contractedAnnularCanonicalLaterUpperMidpointTupleFamily
                eta rho N k hr e (mode e) (hmode e),
              uniform01Measure.real
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
                      ε A N e (mode e) (hmode e) t)) ≤
            ∑ e : Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k,
              ∑ t ∈
                contractedAnnularCanonicalLaterUpperMidpointTupleFamily
                  eta rho N k hr e (mode e) (hmode e),
                (2 * Real.log 2) *
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
                          ε A N e (mode e) (hmode e) t) := by
          apply Finset.sum_le_sum
          intro e _he
          apply Finset.sum_le_sum
          intro t _ht
          apply uniform01MeasureReal_le_gaussMeasureReal
          exact
            (measurableSet_gaussHeterogeneousApproximationTupleEvent
              (Real.log (N : ℝ))
              (gaussPrescribedParityOrientedLower
                (flattenedAnnularParity e)
                (flattenedAnnularSignedLower ε A e)
                (flattenedAnnularSignedUpper ε A e))
              (gaussPrescribedParityOrientedUpper
                (flattenedAnnularParity e)
                (flattenedAnnularSignedLower ε A e)
                (flattenedAnnularSignedUpper ε A e)) t).symmDiff
              (by
                unfold annularUpperRetainedMaskedApproximationDigitEvent
                apply measurableSet_maskedOrderedEventIntersection
                · intro j
                  exact measurableSet_gaussApproximationWindow _ _ _ _
                · intro j
                  exact measurableSet_gaussDigitWindowAt _ _ _ _)
        _ = (2 * Real.log 2) *
              aggregateContractedAnnularUpperRetainedJointFutureReplacementError
                ε A eta rho N k hr mode hmode := by
          unfold
            aggregateContractedAnnularUpperRetainedJointFutureReplacementError
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _he
          rw [Finset.mul_sum]

/-! ## Final bad-moment majorization -/

/-- Finite-`N` scalar majorization of the localized digit transfer.  The
factor `3` consists of the on-good replacement mass and at most two
further copies needed to dominate its contribution on the denominator-bad
set. -/
theorem
    norm_annularContractedUpperRetainedPrefixGoodMixedSum_sub_liveDigitJointSum_le_badMoment
    {ε A eta rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {N grid : ℕ} (hgrid : 0 < grid) (hN : 2 ≤ N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hmargin :
      upperGoodTransferDenominatorTolerance eta rho *
          (annularDepthAmbientSize N : ℝ) ≤
        eta * Real.log (N : ℝ)) :
    ‖annularContractedUpperRetainedPrefixGoodMixedSum
          ε A eta rho N k hr mode hmode -
        annularContractedUpperRetainedLiveDigitJointSum
          ε A eta rho N k hr mode hmode‖ ≤
      3 *
          annularContractedUpperRetainedTaggedUniformReplacementError
            ε A eta rho N k hr mode hmode +
        ∫ x in gaussDenominatorLinearBadEvent 1
            (annularDepthAmbientSize N)
            (upperGoodTransferDenominatorTolerance eta rho),
          2 *
            (Fintype.card
              (Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k) : ℝ) *
            (gaussApproximationWindowCount
              (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
                MixedOccurrenceCount k
            ∂uniform01Measure := by
  let T :=
    AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode
  let bad : Set ℝ :=
    gaussDenominatorLinearBadEvent 1
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  let primary : T → Set ℝ := fun p ↦
    orderedEventIntersection
      (List.ofFn fun j ↦
        gaussApproximationWindow (Real.log (N : ℝ))
          (annularContractedUpperRetainedTimes p j) ε A)
  let error : T → Set ℝ := fun p ↦
    gaussHeterogeneousApproximationTupleEvent
          (Real.log (N : ℝ))
          (gaussPrescribedParityOrientedLower
            (flattenedAnnularParity p.1)
            (flattenedAnnularSignedLower ε A p.1)
            (flattenedAnnularSignedUpper ε A p.1))
          (gaussPrescribedParityOrientedUpper
            (flattenedAnnularParity p.1)
            (flattenedAnnularSignedLower ε A p.1)
            (flattenedAnnularSignedUpper ε A p.1))
          (annularContractedUpperRetainedTimes p) ∆
        annularUpperRetainedMaskedApproximationDigitEvent
          ε A N p.1 (mode p.1) (hmode p.1)
          (annularContractedUpperRetainedTimes p)
  have hprimary : ∀ p ∈ (Finset.univ : Finset T),
      MeasurableSet (primary p) := by
    intro p _hp
    apply measurableSet_orderedEventIntersection
    intro S hS
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hS
    exact measurableSet_gaussApproximationWindow _ _ _ _
  have herror : ∀ p ∈ (Finset.univ : Finset T),
      MeasurableSet (error p) := by
    intro p _hp
    exact
      (measurableSet_gaussHeterogeneousApproximationTupleEvent
        (Real.log (N : ℝ))
        (gaussPrescribedParityOrientedLower
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1))
        (gaussPrescribedParityOrientedUpper
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1))
        (annularContractedUpperRetainedTimes p)).symmDiff
        (by
          unfold annularUpperRetainedMaskedApproximationDigitEvent
          apply measurableSet_maskedOrderedEventIntersection
          · intro j
            exact measurableSet_gaussApproximationWindow _ _ _ _
          · intro j
            exact measurableSet_gaussDigitWindowAt _ _ _ _)
  have hfirst :=
    norm_annularContractedUpperRetainedPrefixGoodMixedSum_sub_liveDigitJointSum_le
      hε hεA hgrid hN hW k hr htime hsigned mode hmode hsmall hmargin
  rw [← gaussDenominatorLinearBadEvent_eq_compl
    1 (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)] at hfirst
  have hunion :
      (∫ x in bad,
          2 * ∑ p : T,
            (primary p ∪ error p).indicator
              (fun _x ↦ (1 : ℝ)) x ∂uniform01Measure) ≤
        (∫ x in bad,
          2 * ∑ p : T,
            (primary p).indicator
              (fun _x ↦ (1 : ℝ)) x ∂uniform01Measure) +
          2 * ∑ p : T, uniform01Measure.real (error p) := by
    simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using!
      setIntegral_two_sum_unionIndicator_le
        uniform01Measure (Finset.univ : Finset T) bad
        primary error hprimary herror
  have hwindow :
      (∫ x in bad,
          2 * ∑ p : T,
            (primary p).indicator
              (fun _x ↦ (1 : ℝ)) x ∂uniform01Measure) ≤
        ∫ x in bad,
          2 *
            (Fintype.card
              (Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k) : ℝ) *
            (gaussApproximationWindowCount
              (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
                MixedOccurrenceCount k
            ∂uniform01Measure := by
    have hleftInt :
        Integrable
          (fun x ↦
            2 * ∑ p : T,
              (primary p).indicator
                (fun _x ↦ (1 : ℝ)) x)
          (uniform01Measure.restrict bad) := by
      apply Integrable.mono_measure _ Measure.restrict_le_self
      apply Integrable.const_mul
      apply integrable_finset_sum
      intro p _hp
      exact (integrable_const (1 : ℝ)).indicator (hprimary p (by simp))
    have hrightInt :
        Integrable
          (fun x ↦
            2 *
              (Fintype.card
                (Fin (MixedOccurrenceCount k) ≃
                  GaussPrefixMixedOccurrence k) : ℝ) *
              (gaussApproximationWindowCount
                (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
                  MixedOccurrenceCount k)
          (uniform01Measure.restrict bad) := by
      apply Integrable.mono_measure _ Measure.restrict_le_self
      exact
        (integrable_gaussApproximationWindowCount_pow
          (Real.log (N : ℝ)) (annularDepthAmbientSize N)
          (MixedOccurrenceCount k) ε A).const_mul
            (2 *
              (Fintype.card
                (Fin (MixedOccurrenceCount k) ≃
                  GaussPrefixMixedOccurrence k) : ℝ))
    apply integral_mono hleftInt hrightInt
    intro x
    dsimp only [T, primary]
    rw [
      sum_annularContractedUpperRetained_taggedWindowIndicators_eq_nested
        k hr mode hmode x]
    have hpoint :=
      sum_annularContractedUpperRetained_windowIndicators_le
        (ε := ε) (A := A) (eta := eta) (rho := rho) (N := N)
        hgrid k hr htime mode hmode (by omega) x
    simpa only [mul_assoc] using!
      mul_le_mul_of_nonneg_left hpoint (by norm_num : (0 : ℝ) ≤ 2)
  refine hfirst.trans ?_
  calc
    (∑ p : T, uniform01Measure.real (error p)) +
        ∫ x in bad,
          2 * ∑ p : T,
            (primary p ∪ error p).indicator
              (fun _x ↦ (1 : ℝ)) x ∂uniform01Measure ≤
      (∑ p : T, uniform01Measure.real (error p)) +
        ((∫ x in bad,
          2 * ∑ p : T,
            (primary p).indicator
              (fun _x ↦ (1 : ℝ)) x ∂uniform01Measure) +
          2 * ∑ p : T, uniform01Measure.real (error p)) :=
      add_le_add_right hunion _
    _ =
      3 * (∑ p : T, uniform01Measure.real (error p)) +
        ∫ x in bad,
          2 * ∑ p : T,
            (primary p).indicator
              (fun _x ↦ (1 : ℝ)) x ∂uniform01Measure := by ring
    _ ≤
      3 * (∑ p : T, uniform01Measure.real (error p)) +
        ∫ x in bad,
          2 *
            (Fintype.card
              (Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k) : ℝ) *
            (gaussApproximationWindowCount
              (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
                MixedOccurrenceCount k
            ∂uniform01Measure :=
      add_le_add_right hwindow _
    _ = _ := by
      rfl

/-- Headline future-digit transfer: for fixed positive contraction
parameters, the delayed-prefix-good full character sum and the live
future-digit joint sum have the same limit.  This combines the complete
joint replacement estimate with the denominator-bad moment bound; no
future rare-window factor is dropped. -/
theorem
    tendsto_annularContractedUpperRetainedPrefixGoodMixedSum_sub_liveDigitJointSum_zero
    {ε A eta rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (heta : 0 < eta) (hrho : 0 < rho)
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
        annularContractedUpperRetainedPrefixGoodMixedSum
            ε A eta rho N k hr mode hmode -
          annularContractedUpperRetainedLiveDigitJointSum
            ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  let replacement : ℕ → ℝ := fun N ↦
    annularContractedUpperRetainedTaggedUniformReplacementError
      ε A eta rho N k hr mode hmode
  let C : ℝ :=
    2 *
      (Fintype.card
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) : ℝ)
  let moment : ℕ → ℝ := fun N ↦
    ∫ x in gaussDenominatorLinearBadEvent 1
        (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho),
      (gaussApproximationWindowCount
        (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
          MixedOccurrenceCount k
      ∂uniform01Measure
  have hreplacement : Tendsto replacement atTop (nhds 0) := by
    simpa only
      [replacement,
        annularContractedUpperRetainedTaggedUniformReplacementError] using!
      tendsto_sum_annularContractedUpperRetained_taggedUniformReplacement_zero
        hε hεA eta rho hgrid k hr htime hsigned mode hmode
  have hmoment : Tendsto moment atTop (nhds 0) := by
    simpa only [moment] using!
      tendsto_gaussApproximationWindowCount_pow_on_denominatorBadEvent
        annularDepthAmbientSize annularDepthAmbientSize
        (MixedOccurrenceCount k) 1
        hr hε hεA
        exists_eventually_annularDepthAmbientSize_le_mul_log
        (by norm_num)
        (upperGoodTransferDenominatorTolerance_pos heta hrho)
        tendsto_annularDepthAmbientSize_atTop
  have hbadMajor :
      Tendsto
        (fun N : ℕ ↦
          ∫ x in gaussDenominatorLinearBadEvent 1
              (annularDepthAmbientSize N)
              (upperGoodTransferDenominatorTolerance eta rho),
            C *
              (gaussApproximationWindowCount
                (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
                  MixedOccurrenceCount k
            ∂uniform01Measure)
        atTop (nhds 0) := by
    have hmul := hmoment.const_mul C
    simpa only [moment, integral_const_mul, mul_zero] using! hmul
  have hmajor :
      Tendsto
        (fun N : ℕ ↦
          3 * replacement N +
            ∫ x in gaussDenominatorLinearBadEvent 1
                (annularDepthAmbientSize N)
                (upperGoodTransferDenominatorTolerance eta rho),
              C *
                (gaussApproximationWindowCount
                  (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
                    MixedOccurrenceCount k
              ∂uniform01Measure)
        atTop (nhds 0) := by
    have hrepScaled : Tendsto (fun N ↦ 3 * replacement N)
        atTop (nhds 0) := by
      simpa only [mul_zero] using! hreplacement.const_mul 3
    simpa only [zero_add] using! hrepScaled.add hbadMajor
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        A / Real.log (N : ℝ) < (1 : ℝ) / 2 := by
    have hlogTwoA :
        ∀ᶠ N : ℕ in atTop,
          2 * A < Real.log (N : ℝ) :=
      tendsto_log_natCast_atTop.eventually_gt_atTop (2 * A)
    filter_upwards
      [hlogTwoA,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
        N htwoA hlog
    exact (div_lt_iff₀ hlog).2 (by linarith)
  have hmargin :=
    eventually_upperGoodTransferDenominatorTolerance_mul_ambient_le_margin
      heta hrho
  have hW :
      ∀ᶠ N : ℕ in atTop, 0 < annularMidpointBandWidth rho N :=
    (tendsto_annularMidpointBandWidth_atTop hrho).eventually_gt_atTop 0
  have hupper :
      ∀ᶠ N : ℕ in atTop,
        ‖annularContractedUpperRetainedPrefixGoodMixedSum
              ε A eta rho N k hr mode hmode -
            annularContractedUpperRetainedLiveDigitJointSum
              ε A eta rho N k hr mode hmode‖ ≤
          3 * replacement N +
            ∫ x in gaussDenominatorLinearBadEvent 1
                (annularDepthAmbientSize N)
                (upperGoodTransferDenominatorTolerance eta rho),
              C *
                (gaussApproximationWindowCount
                  (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
                    MixedOccurrenceCount k
              ∂uniform01Measure := by
    filter_upwards [eventually_ge_atTop 2, hW, hsmall, hmargin] with
        N hN hWN hsmallN hmarginN
    simpa only [replacement, C, mul_assoc] using!
      norm_annularContractedUpperRetainedPrefixGoodMixedSum_sub_liveDigitJointSum_le_badMoment
        hε hεA hgrid hN hWN k hr htime hsigned mode hmode
        hsmallN hmarginN
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _N ↦ norm_nonneg _) hupper hmajor

end

end Erdos1002
