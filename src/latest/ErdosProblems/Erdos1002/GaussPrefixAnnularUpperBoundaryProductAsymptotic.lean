import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperBoundaryDigitMass

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Factorized prefix-boundary products

The prefix-freezing error is factorized before it is summed.  Its boundary
part is therefore a product of a live prefix-boundary probability and the
norm of the complete future mean, not the probability of their
intersection.  This file keeps both factors.  Each exact prefix endpoint
strip is dominated almost everywhere by an enlarged one-digit prefix mask;
the future mean is the mass of the complementary chronological digit mask.
Two independent applications of digit `psi`-mixing then recover one rare
coordinate factor at every chronological index.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 3000000

local instance gaussPrefixAnnularUpperBoundaryProductPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

variable {eta rho ε A : ℝ} {N grid : ℕ}
variable {k : AnnularGridIndex grid → ℕ}
variable {hr : 0 < MixedOccurrenceCount k}
variable
  {mode :
    (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      Fin (MixedOccurrenceCount k) → ℤ}
variable {hmode : ∀ e, mode e ≠ 0}

private theorem measureReal_mono_ae_of_finite_boundaryProduct
    {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsFiniteMeasure mu] {s t : Set α}
    (h : s ≤ᶠ[ae mu] t) :
    mu.real s ≤ mu.real t := by
  rw [measureReal_def, measureReal_def,
    ENNReal.toReal_le_toReal (measure_ne_top mu s) (measure_ne_top mu t)]
  exact measure_mono_ae h

/-- The one-digit event at a chronological coordinate of the dominating
endpoint tuple. -/
def annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (j : Fin (MixedOccurrenceCount k)) : Set ℝ :=
  scaledGaussFirstDigitWindow
    (Real.log (N : ℝ))
    (annularContractedUpperRetainedBoundaryDominatingDigitLower
      ε A eta rho N p i₀ upperEndpoint j)
    (annularContractedUpperRetainedBoundaryDominatingDigitUpper
      ε A eta rho N p i₀ upperEndpoint j)

/-- Prefix half of the dominating chronological digit tuple. -/
def annularContractedUpperRetainedBoundaryPrefixDigitMask
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool) : Set ℝ :=
  chronologicalPrefixDigitMaskEvent
    (annularContractedUpperRetainedDelayedDepth p)
    (annularContractedUpperRetainedTimes p)
    (annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent
      ε A eta rho N p i₀ upperEndpoint)

/-- Future half of the same chronological digit tuple. -/
def annularContractedUpperRetainedBoundaryFutureDigitMask
    (ε A eta rho : ℝ) (N : ℕ)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool) : Set ℝ :=
  chronologicalFutureDigitMaskEvent
    (annularContractedUpperRetainedDelayedDepth p)
    (annularContractedUpperRetainedTimes p)
    (annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent
      ε A eta rho N p i₀ upperEndpoint)

theorem measurableSet_annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool) (j : Fin (MixedOccurrenceCount k)) :
    MeasurableSet
      (annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent
        ε A eta rho N p i₀ upperEndpoint j) :=
  measurableSet_scaledGaussFirstDigitWindow _ _ _

theorem isGaussOneDigitEvent_annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool) (j : Fin (MixedOccurrenceCount k)) :
    IsGaussOneDigitEvent
      (annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent
        ε A eta rho N p i₀ upperEndpoint j) :=
  isGaussOneDigitEvent_scaledGaussFirstDigitWindow _ _ _

/-- On a genuinely future coordinate the dominating event is exactly the
original retained future one-digit event; the endpoint enlargement is
inserted only on prefix coordinates. -/
theorem annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent_of_future
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool) (j : Fin (MixedOccurrenceCount k))
    (hj :
      annularContractedUpperRetainedDelayedDepth p <
        annularContractedUpperRetainedTimes p j) :
    annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent
        ε A eta rho N p i₀ upperEndpoint j =
      scaledGaussFirstDigitWindow
        (Real.log (N : ℝ))
        (annularUpperRetainedOrientedLower ε A
          (annularContractedUpperRetainedUpperTag p) j)
        (annularUpperRetainedOrientedUpper ε A
          (annularContractedUpperRetainedUpperTag p) j) := by
  have hjnot :
      ¬annularContractedUpperRetainedTimes p j ≤
        annularContractedUpperRetainedDelayedDepth p :=
    Nat.not_le.mpr hj
  unfold
    annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent
    annularContractedUpperRetainedBoundaryDominatingDigitLower
    annularContractedUpperRetainedBoundaryDominatingDigitUpper
    annularContractedUpperRetainedBoundaryOrientedLower
    annularContractedUpperRetainedBoundaryOrientedUpper
    annularContractedUpperRetainedBoundarySignedLower
    annularContractedUpperRetainedBoundarySignedUpper
  simp only [if_neg hjnot]
  rw [
    annularContractedUpperRetainedBaseOrientedLower_eq,
    annularContractedUpperRetainedBaseOrientedUpper_eq]
  rfl

/-- The complementary chronological mask and the packaged future tuple
agree almost everywhere.  The only discrepancy is the terminating
continued-fraction exceptional set, on which a neutral `(0,1]` factor can
fail. -/
theorem
    ae_annularContractedUpperRetainedBoundaryFutureDigitMask_eq_futureTuple
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    annularContractedUpperRetainedBoundaryFutureDigitMask
        ε A eta rho N p i₀ upperEndpoint =ᵐ[gaussMeasure]
    annularUpperRetainedFutureDigitTupleEvent ε A
        (annularContractedUpperRetainedUpperTag p) := by
  filter_upwards [ae_nonterminating_gaussMeasure] with x hx
  apply propext
  change
    x ∈ annularContractedUpperRetainedBoundaryFutureDigitMask
        ε A eta rho N p i₀ upperEndpoint ↔
      x ∈ annularUpperRetainedFutureDigitTupleEvent ε A
        (annularContractedUpperRetainedUpperTag p)
  rw [annularContractedUpperRetainedBoundaryFutureDigitMask,
    chronologicalFutureDigitMaskEvent,
    mem_orderedEventIntersection_ofFn_iff,
    mem_annularUpperRetainedFutureDigitTupleEvent_iff
      hgrid htime (annularContractedUpperRetainedUpperTag p) hN hW]
  constructor
  · intro hmask j hjSplit
    have hjFuture :
        annularContractedUpperRetainedDelayedDepth p <
          annularContractedUpperRetainedTimes p j := by
      exact
        (annularUpperRetained_after_delayed_iff_after_split
          hgrid htime
          (annularContractedUpperRetainedUpperTag p) hN hW j).mpr
            hjSplit
    have hjmem := hmask j
    simp only [Set.mem_preimage, if_pos hjFuture] at hjmem
    simpa only [
      annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent_of_future
        p i₀ upperEndpoint j hjFuture] using! hjmem
  · intro hfuture j
    by_cases hj :
        annularContractedUpperRetainedDelayedDepth p <
          annularContractedUpperRetainedTimes p j
    · have hjSplit :
          annularUpperRetainedSplitDepth
              (annularContractedUpperRetainedUpperTag p) <
            annularUpperRetainedTimes
              (annularContractedUpperRetainedUpperTag p) j :=
        (annularUpperRetained_after_delayed_iff_after_split
          hgrid htime
          (annularContractedUpperRetainedUpperTag p) hN hW j).mp hj
      have hjmem := hfuture j hjSplit
      simp only [Set.mem_preimage, if_pos hj]
      simpa only [
        annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent_of_future
          p i₀ upperEndpoint j hj] using! hjmem
    · simp only [Set.mem_preimage, if_neg hj,
        gaussNeutralOneDigitEvent]
      exact gaussOrbit_mem_Ioc_of_not_mem_exceptional
        ⟨hx.1.1, hx.1.2.le⟩
        (not_mem_gaussPrefixExceptional_of_nonterminating
          hx.1 hx.2
          (annularContractedUpperRetainedTimes p j + 1))
        (by omega)

/-- Every exact delayed-prefix endpoint strip is, off the terminating
null set, contained in the enlarged pure one-digit prefix mask.  This is
the point at which the varying approximation coordinate is replaced by
its digit coordinate; all constants are those of the audited uniform
exact-to-digit inclusion. -/
theorem
    ae_annularContractedUpperRetainedPrefixEndpointEvent_subset_prefixDigitMask
    (hε : 0 < ε) (hεA : ε < A) (hgrid : 0 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (hN : 1 < N)
    (hv :
      annularContractedUpperRetainedPrefixValueRadius eta rho N p ≤
        ε / 4)
    (hlargeScale : 128 * A ^ 2 ≤ ε * Real.log (N : ℝ)) :
    ∀ᵐ x ∂gaussMeasure,
      x ∈ annularContractedUpperRetainedPrefixEndpointEvent
          ε A eta rho N p i₀ upperEndpoint →
        x ∈ annularContractedUpperRetainedBoundaryPrefixDigitMask
          ε A eta rho N p i₀ upperEndpoint := by
  have hscale : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  filter_upwards [ae_nonterminating_gaussMeasure] with x hx
  intro hxPrefix
  unfold annularContractedUpperRetainedBoundaryPrefixDigitMask
    chronologicalPrefixDigitMaskEvent
  rw [mem_orderedEventIntersection_ofFn_iff]
  intro j
  by_cases hj :
      annularContractedUpperRetainedTimes p j ≤
        annularContractedUpperRetainedDelayedDepth p
  · let z : GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p) :=
      ⟨p.1 j, by
        have hjtime :=
          congrFun (annularContractedUpperRetainedRealization_times p) j
        change
          ((annularContractedUpperRetainedRealization p).1
              (p.1 j).1 (p.1 j).2 : ℕ) =
            annularContractedUpperRetainedTimes p j at hjtime
        rw [hjtime]
        exact hj⟩
    let i :=
      (annularContractedUpperRetainedPrefixOccurrenceEquiv p).symm z
    let j₀ :=
      annularContractedUpperRetainedPrefixChronologicalIndex p i₀
    have heq :
        (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1 =
          p.1 j := by
      change
        (annularContractedUpperRetainedPrefixOccurrenceEquiv p
            ((annularContractedUpperRetainedPrefixOccurrenceEquiv p).symm
              z)).1 =
          p.1 j
      rw [Equiv.apply_symm_apply]
    have hindex : i = i₀ ↔ j = j₀ := by
      constructor
      · intro hii
        apply p.1.injective
        calc
          p.1 j =
              (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1 :=
            heq.symm
          _ =
              (annularContractedUpperRetainedPrefixOccurrenceEquiv p i₀).1 := by
            rw [hii]
          _ = p.1 j₀ := by
            simpa only [j₀] using!
              (annularContractedUpperRetainedPrefixChronologicalIndex_label
                p i₀).symm
      · intro hjj
        apply
          (annularContractedUpperRetainedPrefixOccurrenceEquiv p).injective
        apply Subtype.ext
        calc
          (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1 =
              p.1 j := heq
          _ = p.1 j₀ := congrArg p.1 hjj
          _ =
              (annularContractedUpperRetainedPrefixOccurrenceEquiv p i₀).1 := by
            simpa only [j₀] using!
              annularContractedUpperRetainedPrefixChronologicalIndex_label
                p i₀
    have hactive : 0 < k (p.1 j).1 := by
      have hjlt := (p.1 j).2.isLt
      omega
    have hactive₀ :
        0 <
          k
            (annularContractedUpperRetainedPrefixOccurrenceEquiv p i₀).1.1 := by
      have hi₀lt :=
        (annularContractedUpperRetainedPrefixOccurrenceEquiv p i₀).1.2.isLt
      omega
    have htimeI :
        ((annularContractedUpperRetainedRealization p).1
            (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1.1
            (annularContractedUpperRetainedPrefixOccurrenceEquiv p i).1.2 :
              ℕ) =
          annularContractedUpperRetainedTimes p j := by
      rw [heq]
      have hjtime :=
        congrFun (annularContractedUpperRetainedRealization_times p) j
      simpa only [fixedOrderMixedTimes] using! hjtime
    have hcenterLower :
        annularContractedUpperRetainedPrefixLower ε A p i₀ =
          flattenedAnnularSignedLower ε A p.1 j₀ := by
      simp only [annularContractedUpperRetainedPrefixLower,
        activeAnnularOccurrenceSignedLower_of_pos hactive₀]
      rw [←
        annularContractedUpperRetainedPrefixChronologicalIndex_label p i₀]
      rfl
    have hcenterUpper :
        annularContractedUpperRetainedPrefixUpper ε A p i₀ =
          flattenedAnnularSignedUpper ε A p.1 j₀ := by
      simp only [annularContractedUpperRetainedPrefixUpper,
        activeAnnularOccurrenceSignedUpper_of_pos hactive₀]
      rw [←
        annularContractedUpperRetainedPrefixChronologicalIndex_label p i₀]
      rfl
    have hlowerI :
        annularContractedUpperRetainedPrefixLower ε A p i =
          flattenedAnnularSignedLower ε A p.1 j := by
      simp only [annularContractedUpperRetainedPrefixLower,
        heq, activeAnnularOccurrenceSignedLower_of_pos hactive]
      rfl
    have hupperI :
        annularContractedUpperRetainedPrefixUpper ε A p i =
          flattenedAnnularSignedUpper ε A p.1 j := by
      simp only [annularContractedUpperRetainedPrefixUpper,
        heq, activeAnnularOccurrenceSignedUpper_of_pos hactive]
      rfl
    rw [annularContractedUpperRetainedPrefixEndpointEvent,
      closedEndpointStripWindowTupleEvent, closedWindowTupleEvent]
      at hxPrefix
    have hi := Set.mem_iInter.mp hxPrefix i
    have hsignedWindow :
        x ∈ gaussSignedApproximationWindow
          (Real.log (N : ℝ))
          (annularContractedUpperRetainedTimes p j)
          (annularContractedUpperRetainedBoundarySignedLower
            ε A eta rho N p i₀ upperEndpoint j)
          (annularContractedUpperRetainedBoundarySignedUpper
            ε A eta rho N p i₀ upperEndpoint j) := by
      refine ⟨⟨hx.1.1, hx.1.2.le⟩, ?_⟩
      change
        annularContractedUpperRetainedPrefixCoordinate p x i ∈
          Icc
            (if i = i₀ then
              (if upperEndpoint then
                  annularContractedUpperRetainedPrefixUpper ε A p i₀
                else
                  annularContractedUpperRetainedPrefixLower ε A p i₀) -
                annularContractedUpperRetainedPrefixValueRadius eta rho N p
            else
              annularContractedUpperRetainedPrefixLower ε A p i -
                annularContractedUpperRetainedPrefixValueRadius eta rho N p)
            (if i = i₀ then
              (if upperEndpoint then
                  annularContractedUpperRetainedPrefixUpper ε A p i₀
                else
                  annularContractedUpperRetainedPrefixLower ε A p i₀) +
                annularContractedUpperRetainedPrefixValueRadius eta rho N p
            else
              annularContractedUpperRetainedPrefixUpper ε A p i +
                annularContractedUpperRetainedPrefixValueRadius eta rho N p)
        at hi
      change
        gaussSignedScaledApproximationCoordinate
            (Real.log (N : ℝ))
            (annularContractedUpperRetainedTimes p j) x ∈
          Icc
            (annularContractedUpperRetainedBoundarySignedLower
              ε A eta rho N p i₀ upperEndpoint j)
            (annularContractedUpperRetainedBoundarySignedUpper
              ε A eta rho N p i₀ upperEndpoint j)
      simpa only [
        annularContractedUpperRetainedPrefixCoordinate,
        heq,
        hlowerI, hupperI,
        gaussPrefixMarkedPoint_value_eq_signedScaledApproximation,
        htimeI,
        annularContractedUpperRetainedBoundarySignedLower,
        annularContractedUpperRetainedBoundarySignedUpper,
        if_pos hj,
        hindex,
        j₀,
        annularContractedUpperRetainedBoundarySignedCenter,
        hcenterLower, hcenterUpper] using! hi
    rw [gaussSignedApproximationWindow_eq_oriented] at hsignedWindow
    have hexact :
        x ∈ gaussApproximationWindow
          (Real.log (N : ℝ))
          (annularContractedUpperRetainedTimes p j)
          (annularContractedUpperRetainedBoundaryOrientedLower
            ε A eta rho N p i₀ upperEndpoint j)
          (annularContractedUpperRetainedBoundaryOrientedUpper
            ε A eta rho N p i₀ upperEndpoint j) := by
      simpa only [
        annularContractedUpperRetainedBoundaryOrientedLower,
        annularContractedUpperRetainedBoundaryOrientedUpper] using!
        hsignedWindow
    have hlower :
        0 <
          annularContractedUpperRetainedBoundaryOrientedLower
            ε A eta rho N p i₀ upperEndpoint j := by
      exact lt_of_lt_of_le (by linarith)
        (annularContractedUpperRetainedBoundaryOrientedLower_ge_half
          hε hεA hgrid hsigned p i₀ upperEndpoint hv j)
    have hupper :
        annularContractedUpperRetainedBoundaryOrientedLower
            ε A eta rho N p i₀ upperEndpoint j <
          annularContractedUpperRetainedBoundaryOrientedUpper
            ε A eta rho N p i₀ upperEndpoint j :=
      annularContractedUpperRetainedBoundaryOrientedLower_lt_upper
        hεA hgrid p i₀ upperEndpoint
          (annularContractedUpperRetainedPrefixValueRadius_pos p hN) j
    have hlarge :
        16 *
            (annularContractedUpperRetainedBoundaryOrientedUpper
              ε A eta rho N p i₀ upperEndpoint j) ^ 2 ≤
          annularContractedUpperRetainedBoundaryOrientedLower
              ε A eta rho N p i₀ upperEndpoint j *
            Real.log (N : ℝ) :=
      annularContractedUpperRetainedBoundary_large
        hε hεA hgrid hsigned p i₀ upperEndpoint hv hscale hlargeScale j
    have hdigitOrExceptional :=
      union_gaussApproximationWindow_gaussDigitWindowAt_subset
        hscale hlower hupper hlarge (Or.inl hexact)
    rcases hdigitOrExceptional with hexceptional | hdigit
    · exact False.elim <|
        (not_mem_gaussPrefixExceptional_of_nonterminating
          hx.1 hx.2
          (annularContractedUpperRetainedTimes p j + 1)) hexceptional
    · simpa only [
        Set.mem_preimage,
        if_pos hj,
        annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent,
        annularContractedUpperRetainedBoundaryDominatingDigitLower,
        annularContractedUpperRetainedBoundaryDominatingDigitUpper,
        gaussEnlargedDigitWindow] using! hdigit
  · have hjFuture :
        annularContractedUpperRetainedDelayedDepth p <
          annularContractedUpperRetainedTimes p j :=
      Nat.lt_of_not_ge hj
    simp only [Set.mem_preimage, if_neg hj,
      gaussNeutralOneDigitEvent]
    exact gaussOrbit_mem_Ioc_of_not_mem_exceptional
      ⟨hx.1.1, hx.1.2.le⟩
      (not_mem_gaussPrefixExceptional_of_nonterminating
        hx.1 hx.2
        (annularContractedUpperRetainedTimes p j + 1))
      (by omega)

/-- The packaged future mean is exactly the (nonnegative real) Gauss mass
of the direct future digit event. -/
theorem norm_annularContractedUpperRetainedFutureMean_eq_measureReal
    (ε A eta rho : ℝ) (N : ℕ)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    ‖annularContractedUpperRetainedFutureMean
        ε A eta rho N k hr mode hmode p‖ =
      gaussMeasure.real
        (annularUpperRetainedFutureDigitTupleEvent ε A
          (annularContractedUpperRetainedUpperTag p)) := by
  unfold annularContractedUpperRetainedFutureMean
    gaussLateFutureDigitBlockMean
  rw [show
    (fun x ↦
      gaussFutureDigitBlockIndicator
        (annularContractedUpperRetainedDelayedDepth p +
          annularContractedUpperRetainedMixingGap rho N)
        (annularContractedUpperRetainedFutureTime p)
        (annularContractedUpperRetainedFutureDigitEvent ε A p) x) =
      fun x ↦
        (annularUpperRetainedFutureDigitTupleEvent ε A
          (annularContractedUpperRetainedUpperTag p)).indicator
            (fun _ ↦ (1 : ℂ)) x by
    funext x
    simpa only [
      annularContractedUpperRetained_delayedDepth_add_mixingGap,
      annularContractedUpperRetainedFutureTime,
      annularContractedUpperRetainedFutureDigitEvent,
      annularContractedUpperRetainedUpperTag] using!
      annularUpperRetainedFutureDigitBlock_eq_eventIndicator
        (ε := ε) (A := A)
        (annularContractedUpperRetainedUpperTag p) x]
  rw [MeasureTheory.integral_indicator_const]
  · rw [norm_smul, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg measureReal_nonneg]
  · exact measurableSet_annularUpperRetainedFutureDigitTupleEvent
      (ε := ε) (A := A)
      (annularContractedUpperRetainedUpperTag p)

/-- Version of the preceding identity using the complementary
chronological mask attached to a particular endpoint strip. -/
theorem norm_annularContractedUpperRetainedFutureMean_eq_boundaryFutureMask_measureReal
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    ‖annularContractedUpperRetainedFutureMean
        ε A eta rho N k hr mode hmode p‖ =
      gaussMeasure.real
        (annularContractedUpperRetainedBoundaryFutureDigitMask
          ε A eta rho N p i₀ upperEndpoint) := by
  rw [norm_annularContractedUpperRetainedFutureMean_eq_measureReal]
  have hmeasure :=
    (ae_annularContractedUpperRetainedBoundaryFutureDigitMask_eq_futureTuple
      (ε := ε) (A := A) hgrid htime p i₀ upperEndpoint hN hW).measure_eq
  simpa only [measureReal_def] using!
    congrArg ENNReal.toReal hmeasure.symm

/-- One endpoint's factorized prefix--future mass majorant.  Relative to
the full tuple mass estimate it pays one additional, fixed chronological
mixing factor. -/
def annularUpperBoundaryFactorizedMassBound
    (r : ℕ) (scale A : ℝ) : ℝ :=
  (1 + gaussDigitExponentialRate 1) ^ (r - 1) *
    annularUpperBoundaryDominatingDigitMassBound r scale A

theorem annularUpperBoundaryFactorizedMassBound_eq_coordinate
    (r : ℕ) (scale A : ℝ) :
    annularUpperBoundaryFactorizedMassBound r scale A =
      (1 + gaussDigitExponentialRate 1) ^ (2 * (r - 1)) *
        annularUpperBoundaryDominatingDigitCoordinateMassBound
          r scale A := by
  unfold annularUpperBoundaryFactorizedMassBound
    annularUpperBoundaryDominatingDigitMassBound
    annularUpperBoundaryDominatingDigitCoordinateMassBound
  rw [two_mul, pow_add]
  ring

theorem annularUpperBoundaryFactorizedMassBound_nonneg
    (r : ℕ) {scale A : ℝ} (hscale : 0 < scale) (hA : 0 ≤ A) :
    0 ≤ annularUpperBoundaryFactorizedMassBound r scale A := by
  unfold annularUpperBoundaryFactorizedMassBound
  exact mul_nonneg
    (pow_nonneg
      (by
        have hrate := gaussDigitExponentialRate_nonnegative 1
        linarith) _)
    (annularUpperBoundaryDominatingDigitMassBound_nonneg
      r hscale hA)

theorem tendsto_annularDepth_pow_mul_boundaryFactorizedMassBound_zero
    (r : ℕ) (hr : 0 < r) (A : ℝ) :
    Tendsto
      (fun N : ℕ ↦
        (annularDepthAmbientSize N : ℝ) ^ r *
          annularUpperBoundaryFactorizedMassBound
            r (Real.log (N : ℝ)) A)
      atTop (nhds 0) := by
  let C := (1 + gaussDigitExponentialRate 1) ^ (r - 1)
  have h :=
    (tendsto_const_nhds.mul
      (tendsto_annularDepth_pow_mul_boundaryDominatingDigitMassBound_zero
        r hr A) :
      Tendsto
        (fun N : ℕ ↦
          C *
            ((annularDepthAmbientSize N : ℝ) ^ r *
              annularUpperBoundaryDominatingDigitMassBound
                r (Real.log (N : ℝ)) A))
        atTop (nhds (C * 0)))
  simpa only [C, mul_zero,
    annularUpperBoundaryFactorizedMassBound] using!
    h.congr' (Eventually.of_forall fun _N ↦ by ring)

/-- Sharp bound for one exact prefix endpoint probability multiplied by
the norm of its complete future mean. -/
theorem
    gaussMeasure_real_prefixEndpoint_mul_norm_futureMean_le_factorizedMassBound
    (hε : 0 < ε) (hεA : ε < A) (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (upperEndpoint : Bool)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (hscaleOne : 1 ≤ Real.log (N : ℝ))
    (hv :
      annularContractedUpperRetainedPrefixValueRadius eta rho N p ≤
        ε / 4)
    (hvScale :
      annularContractedUpperRetainedPrefixValueRadius eta rho N p *
          Real.log (N : ℝ) ≤
        (2 * A) ^ 2)
    (hlargeScale : 128 * A ^ 2 ≤ ε * Real.log (N : ℝ)) :
    gaussMeasure.real
          (annularContractedUpperRetainedPrefixEndpointEvent
            ε A eta rho N p i₀ upperEndpoint) *
        ‖annularContractedUpperRetainedFutureMean
          ε A eta rho N k hr mode hmode p‖ ≤
      annularUpperBoundaryFactorizedMassBound
        (MixedOccurrenceCount k) (Real.log (N : ℝ)) A := by
  let events :=
    annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent
      ε A eta rho N p i₀ upperEndpoint
  let times := annularContractedUpperRetainedTimes p
  let prefixMask :=
    annularContractedUpperRetainedBoundaryPrefixDigitMask
      ε A eta rho N p i₀ upperEndpoint
  let futureMask :=
    annularContractedUpperRetainedBoundaryFutureDigitMask
      ε A eta rho N p i₀ upperEndpoint
  have hprefixMass :
      gaussMeasure.real
          (annularContractedUpperRetainedPrefixEndpointEvent
            ε A eta rho N p i₀ upperEndpoint) ≤
        gaussMeasure.real prefixMask := by
    apply measureReal_mono_ae_of_finite_boundaryProduct gaussMeasure
    simpa only [prefixMask] using!
      ae_annularContractedUpperRetainedPrefixEndpointEvent_subset_prefixDigitMask
        hε hεA hgrid hsigned p i₀ upperEndpoint hN hv hlargeScale
  have hfutureNorm :
      ‖annularContractedUpperRetainedFutureMean
          ε A eta rho N k hr mode hmode p‖ =
        gaussMeasure.real futureMask := by
    simpa only [futureMask] using!
      norm_annularContractedUpperRetainedFutureMean_eq_boundaryFutureMask_measureReal
        (ε := ε) (A := A) hgrid htime p i₀ upperEndpoint hN hW
  have hgap : ∀ i j, i < j → times i + 1 ≤ times j := by
    simpa only [times] using!
      contractedAnnularCanonicalLaterUpperMidpointTupleFamily_chronological
        k hr p.1 (mode p.1) (hmode p.1)
          (annularContractedUpperRetainedTimes p) p.2.2
  have hmasks :=
    gaussMeasure_real_prefixMask_mul_futureMask_le
      gaussDigitPsiMixing_exponential hr
      (annularContractedUpperRetainedDelayedDepth p)
      times events 1 (by norm_num)
      (fun j ↦ by
        simpa only [events] using!
          measurableSet_annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent
            (ε := ε) (A := A) p i₀ upperEndpoint j)
      (fun j ↦ by
        simpa only [events] using!
          isGaussOneDigitEvent_annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent
            (ε := ε) (A := A) p i₀ upperEndpoint j)
      hgap (gaussDigitExponentialRate_nonnegative 1)
  have hprod :=
    finprod_gaussMeasure_real_annularContractedUpperRetainedBoundaryDominatingDigit_le
      hε hεA hgrid hsigned p i₀ upperEndpoint
        hN hscaleOne hv hvScale hlargeScale
  calc
    gaussMeasure.real
          (annularContractedUpperRetainedPrefixEndpointEvent
            ε A eta rho N p i₀ upperEndpoint) *
        ‖annularContractedUpperRetainedFutureMean
          ε A eta rho N k hr mode hmode p‖ ≤
      gaussMeasure.real prefixMask *
        gaussMeasure.real futureMask := by
      rw [hfutureNorm]
      exact mul_le_mul_of_nonneg_right hprefixMass measureReal_nonneg
    _ ≤
      (1 + gaussDigitExponentialRate 1) ^
          (2 * (MixedOccurrenceCount k - 1)) *
        ∏ j : Fin (MixedOccurrenceCount k),
          gaussMeasure.real (events j) := by
      simpa only [prefixMask, futureMask, times, events] using! hmasks
    _ ≤
      (1 + gaussDigitExponentialRate 1) ^
          (2 * (MixedOccurrenceCount k - 1)) *
        annularUpperBoundaryDominatingDigitCoordinateMassBound
          (MixedOccurrenceCount k) (Real.log (N : ℝ)) A := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [events,
          annularContractedUpperRetainedBoundaryDominatingDigitBaseEvent]
          using! hprod
      · exact pow_nonneg
          (by
            have hrate := gaussDigitExponentialRate_nonnegative 1
            linarith) _
    _ = _ := by
      rw [annularUpperBoundaryFactorizedMassBound_eq_coordinate]

/-- The denominator-good prefix boundary is the union of its two endpoint
strips.  Dropping only the denominator-good restriction and applying the
previous endpoint estimate gives the required factor `2`; the future mean
remains present in every summand. -/
theorem
    gaussMeasure_real_goodPrefixBoundary_mul_norm_futureMean_le
    (hε : 0 < ε) (hεA : ε < A) (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (i₀ : Fin (Fintype.card
      (GaussPrefixMixedPrefixOccurrence N k
        (annularContractedUpperRetainedRealization p).1
        (annularContractedUpperRetainedDelayedDepth p))))
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (hscaleOne : 1 ≤ Real.log (N : ℝ))
    (hv :
      annularContractedUpperRetainedPrefixValueRadius eta rho N p ≤
        ε / 4)
    (hvScale :
      annularContractedUpperRetainedPrefixValueRadius eta rho N p *
          Real.log (N : ℝ) ≤
        (2 * A) ^ 2)
    (hlargeScale : 128 * A ^ 2 ≤ ε * Real.log (N : ℝ)) :
    gaussMeasure.real
          (gaussDenominatorPrefixGoodEvent
              (annularContractedUpperRetainedDelayedDepth p)
              (annularDepthAmbientSize N)
              (upperGoodTransferDenominatorTolerance eta rho) ∩
            annularContractedUpperRetainedPrefixBoundaryEvent
              ε A eta rho N p i₀) *
        ‖annularContractedUpperRetainedFutureMean
          ε A eta rho N k hr mode hmode p‖ ≤
      2 * annularUpperBoundaryFactorizedMassBound
        (MixedOccurrenceCount k) (Real.log (N : ℝ)) A := by
  have hunion :
      annularContractedUpperRetainedPrefixBoundaryEvent
          ε A eta rho N p i₀ =
        annularContractedUpperRetainedPrefixEndpointEvent
            ε A eta rho N p i₀ false ∪
          annularContractedUpperRetainedPrefixEndpointEvent
            ε A eta rho N p i₀ true := by
    unfold annularContractedUpperRetainedPrefixBoundaryEvent
      annularContractedUpperRetainedPrefixEndpointEvent
    simpa only [Bool.false_eq_true, ↓reduceIte] using!
      closedBoundaryWindowTupleEvent_eq_union_endpointStrips
        (annularContractedUpperRetainedPrefixLower ε A p)
        (annularContractedUpperRetainedPrefixUpper ε A p)
        (annularContractedUpperRetainedPrefixCoordinate p)
        (annularContractedUpperRetainedPrefixValueRadius eta rho N p) i₀
  have hprefix :
      gaussMeasure.real
          (gaussDenominatorPrefixGoodEvent
              (annularContractedUpperRetainedDelayedDepth p)
              (annularDepthAmbientSize N)
              (upperGoodTransferDenominatorTolerance eta rho) ∩
            annularContractedUpperRetainedPrefixBoundaryEvent
              ε A eta rho N p i₀) ≤
        gaussMeasure.real
            (annularContractedUpperRetainedPrefixEndpointEvent
                ε A eta rho N p i₀ false) +
          gaussMeasure.real
            (annularContractedUpperRetainedPrefixEndpointEvent
                ε A eta rho N p i₀ true) := by
    calc
      gaussMeasure.real
          (gaussDenominatorPrefixGoodEvent
              (annularContractedUpperRetainedDelayedDepth p)
              (annularDepthAmbientSize N)
              (upperGoodTransferDenominatorTolerance eta rho) ∩
            annularContractedUpperRetainedPrefixBoundaryEvent
              ε A eta rho N p i₀) ≤
        gaussMeasure.real
          (annularContractedUpperRetainedPrefixBoundaryEvent
            ε A eta rho N p i₀) :=
        measureReal_mono Set.inter_subset_right
      _ =
        gaussMeasure.real
          (annularContractedUpperRetainedPrefixEndpointEvent
              ε A eta rho N p i₀ false ∪
            annularContractedUpperRetainedPrefixEndpointEvent
              ε A eta rho N p i₀ true) := by rw [hunion]
      _ ≤ _ := measureReal_union_le _ _
  have hlower :=
    gaussMeasure_real_prefixEndpoint_mul_norm_futureMean_le_factorizedMassBound
      hε hεA hgrid htime hsigned p i₀ false hN hW hscaleOne
        hv hvScale hlargeScale
  have hupper :=
    gaussMeasure_real_prefixEndpoint_mul_norm_futureMean_le_factorizedMassBound
      hε hεA hgrid htime hsigned p i₀ true hN hW hscaleOne
        hv hvScale hlargeScale
  calc
    gaussMeasure.real
          (gaussDenominatorPrefixGoodEvent
              (annularContractedUpperRetainedDelayedDepth p)
              (annularDepthAmbientSize N)
              (upperGoodTransferDenominatorTolerance eta rho) ∩
            annularContractedUpperRetainedPrefixBoundaryEvent
              ε A eta rho N p i₀) *
        ‖annularContractedUpperRetainedFutureMean
          ε A eta rho N k hr mode hmode p‖ ≤
      (gaussMeasure.real
            (annularContractedUpperRetainedPrefixEndpointEvent
                ε A eta rho N p i₀ false) +
          gaussMeasure.real
            (annularContractedUpperRetainedPrefixEndpointEvent
                ε A eta rho N p i₀ true)) *
        ‖annularContractedUpperRetainedFutureMean
          ε A eta rho N k hr mode hmode p‖ :=
      mul_le_mul_of_nonneg_right hprefix (norm_nonneg _)
    _ =
      gaussMeasure.real
            (annularContractedUpperRetainedPrefixEndpointEvent
              ε A eta rho N p i₀ false) *
          ‖annularContractedUpperRetainedFutureMean
            ε A eta rho N k hr mode hmode p‖ +
        gaussMeasure.real
            (annularContractedUpperRetainedPrefixEndpointEvent
              ε A eta rho N p i₀ true) *
          ‖annularContractedUpperRetainedFutureMean
            ε A eta rho N k hr mode hmode p‖ := by ring
    _ ≤
      annularUpperBoundaryFactorizedMassBound
          (MixedOccurrenceCount k) (Real.log (N : ℝ)) A +
        annularUpperBoundaryFactorizedMassBound
          (MixedOccurrenceCount k) (Real.log (N : ℝ)) A :=
      add_le_add hlower hupper
    _ = _ := by ring

/-- The complete factorized prefix-boundary contribution tends to zero.
This is stated with the literal good-prefix intersection so that the
factorized assembly can use it by definitional simplification. -/
theorem
    tendsto_sum_gaussMeasure_real_goodPrefixBoundary_mul_norm_futureMean_zero
    {eta rho ε A : ℝ} (hrho : 0 < rho)
    (hε : 0 < ε) (hεA : ε < A)
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
          ∑ i : Fin (Fintype.card
            (GaussPrefixMixedPrefixOccurrence N k
              (annularContractedUpperRetainedRealization p).1
              (annularContractedUpperRetainedDelayedDepth p))),
            gaussMeasure.real
                (gaussDenominatorPrefixGoodEvent
                    (annularContractedUpperRetainedDelayedDepth p)
                    (annularDepthAmbientSize N)
                    (upperGoodTransferDenominatorTolerance eta rho) ∩
                  annularContractedUpperRetainedPrefixBoundaryEvent
                    ε A eta rho N p i) *
              ‖annularContractedUpperRetainedFutureMean
                ε A eta rho N k hr mode hmode p‖)
      atTop (nhds 0) := by
  let r := MixedOccurrenceCount k
  let Ctag :=
    Fintype.card
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
  let C : ℝ := (Ctag : ℝ) * (r : ℝ) * 2
  let upper : ℕ → ℝ := fun N ↦
    C * (annularDepthAmbientSize N : ℝ) ^ r *
      annularUpperBoundaryFactorizedMassBound
        r (Real.log (N : ℝ)) A
  have hupperZero : Tendsto upper atTop (nhds 0) := by
    have h :=
      (tendsto_annularDepth_pow_mul_boundaryFactorizedMassBound_zero
        r hr A).const_mul C
    simpa only [upper, mul_assoc, mul_zero] using! h
  have hN : ∀ᶠ N : ℕ in atTop, 1 < N := eventually_ge_atTop 2
  have hW :
      ∀ᶠ N : ℕ in atTop, 0 < annularMidpointBandWidth rho N :=
    (tendsto_annularMidpointBandWidth_atTop hrho).eventually_gt_atTop 0
  have hscaleOne :
      ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    tendsto_log_natCast_atTop.eventually (eventually_ge_atTop 1)
  have henvSmall :
      ∀ᶠ N : ℕ in atTop,
        annularUpperFreezingValueRadiusEnvelope rho N < ε / 4 :=
    (tendsto_annularUpperFreezingValueRadiusEnvelope_zero hrho
      ).eventually_lt_const (by linarith)
  have hscaleEnvelopeZero :=
    tendsto_const_mul_annularDepth_pow_mul_valueRadiusEnvelope_zero
      gaussRoofMean 1 gaussRoofMean_pos.le hrho
  have hscaleEnvelopeSmall :
      ∀ᶠ N : ℕ in atTop,
        gaussRoofMean * (annularDepthAmbientSize N : ℝ) ^ 1 *
            annularUpperFreezingValueRadiusEnvelope rho N <
          (2 * A) ^ 2 :=
    hscaleEnvelopeZero.eventually_lt_const (by
      have hA : 0 < A := hε.trans hεA
      positivity)
  have hlargeScale :
      ∀ᶠ N : ℕ in atTop,
        128 * A ^ 2 ≤ ε * Real.log (N : ℝ) := by
    have hlogLarge :=
      tendsto_log_natCast_atTop.eventually_gt_atTop
        (128 * A ^ 2 / ε)
    filter_upwards [hlogLarge] with N hlogLargeN
    have hmul := (div_lt_iff₀ hε).mp hlogLargeN
    nlinarith
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦ by
      exact Finset.sum_nonneg fun _p _hp ↦
        Finset.sum_nonneg fun _i _hi ↦
          mul_nonneg measureReal_nonneg (norm_nonneg _)
  · filter_upwards [hN, hW, hscaleOne, henvSmall,
      hscaleEnvelopeSmall, hlargeScale] with
      N hN hW hscaleOne henvSmall hscaleEnvelopeSmall hlargeScale
    have hlog : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast hN)
    have hA : 0 < A := hε.trans hεA
    have hboundNonneg :
        0 ≤ annularUpperBoundaryFactorizedMassBound
          r (Real.log (N : ℝ)) A :=
      annularUpperBoundaryFactorizedMassBound_nonneg r hlog hA.le
    have hlogUpper :
        Real.log (N : ℝ) ≤
          gaussRoofMean * (annularDepthAmbientSize N : ℝ) := by
      have hraw :=
        log_natCast_le_ambient_sub_one_mul_gaussRoofMean
          (show 1 ≤ N by omega)
      nlinarith [gaussRoofMean_pos]
    have htagCard :=
      card_annularContractedUpperRetainedTaggedTuple_le_ambient
        eta rho N hgrid k hr htime mode hmode hN
    have htagCardReal :
        (Fintype.card
            (AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode) : ℝ) ≤
          (Ctag : ℝ) *
            (annularDepthAmbientSize N : ℝ) ^ r := by
      exact_mod_cast htagCard
    have hvBound :
        ∀ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          annularContractedUpperRetainedPrefixValueRadius
              eta rho N p ≤ ε / 4 := by
      intro p
      exact
        (gaussPrefixGoodValueFreezingRadius_le_annularUpperEnvelope
          hgrid k hr htime mode hmode hN hW p).trans henvSmall.le
    have hvScale :
        ∀ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          annularContractedUpperRetainedPrefixValueRadius eta rho N p *
              Real.log (N : ℝ) ≤
            (2 * A) ^ 2 := by
      intro p
      have hvEnv :=
        gaussPrefixGoodValueFreezingRadius_le_annularUpperEnvelope
          hgrid k hr htime mode hmode hN hW p
      have henvNonneg :
          0 ≤ annularUpperFreezingValueRadiusEnvelope rho N := by
        unfold annularUpperFreezingValueRadiusEnvelope
        have hlogNonneg : 0 ≤ Real.log (N : ℝ) := hlog.le
        positivity
      calc
        annularContractedUpperRetainedPrefixValueRadius eta rho N p *
              Real.log (N : ℝ) ≤
            annularUpperFreezingValueRadiusEnvelope rho N *
              Real.log (N : ℝ) :=
          mul_le_mul_of_nonneg_right hvEnv hlog.le
        _ ≤
            gaussRoofMean * (annularDepthAmbientSize N : ℝ) *
              annularUpperFreezingValueRadiusEnvelope rho N := by
          simpa only [mul_comm, mul_left_comm, mul_assoc] using!
            mul_le_mul_of_nonneg_left hlogUpper henvNonneg
        _ ≤ (2 * A) ^ 2 := by
          simpa only [pow_one, mul_assoc] using! hscaleEnvelopeSmall.le
    calc
      (∑ p : AnnularContractedUpperRetainedTaggedTuple
          eta rho N k hr mode hmode,
        ∑ i : Fin (Fintype.card
          (GaussPrefixMixedPrefixOccurrence N k
            (annularContractedUpperRetainedRealization p).1
            (annularContractedUpperRetainedDelayedDepth p))),
          gaussMeasure.real
              (gaussDenominatorPrefixGoodEvent
                  (annularContractedUpperRetainedDelayedDepth p)
                  (annularDepthAmbientSize N)
                  (upperGoodTransferDenominatorTolerance eta rho) ∩
                annularContractedUpperRetainedPrefixBoundaryEvent
                  ε A eta rho N p i) *
            ‖annularContractedUpperRetainedFutureMean
              ε A eta rho N k hr mode hmode p‖) ≤
        ∑ _p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          (r : ℝ) *
            (2 * annularUpperBoundaryFactorizedMassBound
              r (Real.log (N : ℝ)) A) := by
        apply Finset.sum_le_sum
        intro p _hp
        calc
          (∑ i : Fin (Fintype.card
              (GaussPrefixMixedPrefixOccurrence N k
                (annularContractedUpperRetainedRealization p).1
                (annularContractedUpperRetainedDelayedDepth p))),
            gaussMeasure.real
                (gaussDenominatorPrefixGoodEvent
                    (annularContractedUpperRetainedDelayedDepth p)
                    (annularDepthAmbientSize N)
                    (upperGoodTransferDenominatorTolerance eta rho) ∩
                  annularContractedUpperRetainedPrefixBoundaryEvent
                    ε A eta rho N p i) *
              ‖annularContractedUpperRetainedFutureMean
                ε A eta rho N k hr mode hmode p‖) ≤
            ∑ _i : Fin (Fintype.card
                (GaussPrefixMixedPrefixOccurrence N k
                  (annularContractedUpperRetainedRealization p).1
                  (annularContractedUpperRetainedDelayedDepth p))),
              2 * annularUpperBoundaryFactorizedMassBound
                r (Real.log (N : ℝ)) A := by
              apply Finset.sum_le_sum
              intro i _hi
              exact
                gaussMeasure_real_goodPrefixBoundary_mul_norm_futureMean_le
                  hε hεA hgrid htime hsigned p i hN hW hscaleOne
                    (hvBound p) (hvScale p) hlargeScale
          _ =
            (Fintype.card
                (GaussPrefixMixedPrefixOccurrence N k
                  (annularContractedUpperRetainedRealization p).1
                  (annularContractedUpperRetainedDelayedDepth p)) : ℝ) *
              (2 * annularUpperBoundaryFactorizedMassBound
                r (Real.log (N : ℝ)) A) := by simp
          _ ≤
            (r : ℝ) *
              (2 * annularUpperBoundaryFactorizedMassBound
                r (Real.log (N : ℝ)) A) := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by norm_num)
              hboundNonneg)
            exact_mod_cast card_gaussPrefixMixedPrefixOccurrence_le p
      _ =
        (Fintype.card
            (AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode) : ℝ) *
          ((r : ℝ) *
            (2 * annularUpperBoundaryFactorizedMassBound
              r (Real.log (N : ℝ)) A)) := by simp
      _ ≤
        ((Ctag : ℝ) *
            (annularDepthAmbientSize N : ℝ) ^ r) *
          ((r : ℝ) *
            (2 * annularUpperBoundaryFactorizedMassBound
              r (Real.log (N : ℝ)) A)) := by
        exact mul_le_mul_of_nonneg_right htagCardReal
          (mul_nonneg (Nat.cast_nonneg r)
            (mul_nonneg (by norm_num) hboundNonneg))
      _ = upper N := by
        dsimp only [upper, C]
        ring
  · exact hupperZero

end

end Erdos1002
