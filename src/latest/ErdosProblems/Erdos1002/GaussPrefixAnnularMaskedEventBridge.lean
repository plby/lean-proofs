import ErdosProblems.Erdos1002.GaussPrefixAnnularContractedJointReplacement
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperShallowCarrier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Event bridge for the upper retained future replacement

The quantitative masked replacement theorem is stated for one complete
heterogeneous approximation event.  The late argument subsequently writes
that event as an exact prefix event times a future event.  This file proves
the required identities literally.  In particular, the prefix event remains
attached while the future exact windows are replaced by digit windows.
-/

open Finset MeasureTheory Set
open scoped BigOperators symmDiff

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularMaskedEventBridgePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

variable {rho ε A : ℝ} {N grid : ℕ}
variable {k : AnnularGridIndex grid → ℕ}
variable {hr : 0 < MixedOccurrenceCount k}
variable
  {mode :
    (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      Fin (MixedOccurrenceCount k) → ℤ}
variable {hmode : ∀ e, mode e ≠ 0}

/-- An exact approximation coordinate is retained precisely when its
chronological depth is at or before the midpoint split. -/
def annularUpperRetainedPrefixApproximationCoordinateEvent
    (ε A : ℝ)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) : Set ℝ :=
  if annularUpperRetainedTimes p j ≤
      annularUpperRetainedSplitDepth p then
    gaussApproximationWindow
      (Real.log (N : ℝ))
      (annularUpperRetainedTimes p j)
      (annularUpperRetainedOrientedLower ε A p j)
      (annularUpperRetainedOrientedUpper ε A p j)
  else Set.univ

/-- Simultaneous exact prefix event at the midpoint split. -/
def annularUpperRetainedPrefixApproximationEvent
    (ε A : ℝ)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun j ↦
    annularUpperRetainedPrefixApproximationCoordinateEvent ε A p j

theorem mem_annularUpperRetainedPrefixApproximationEvent_iff
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (x : ℝ) :
    x ∈ annularUpperRetainedPrefixApproximationEvent ε A p ↔
      ∀ j : Fin (MixedOccurrenceCount k),
        annularUpperRetainedTimes p j ≤
            annularUpperRetainedSplitDepth p →
          x ∈ gaussApproximationWindow
            (Real.log (N : ℝ))
            (annularUpperRetainedTimes p j)
            (annularUpperRetainedOrientedLower ε A p j)
            (annularUpperRetainedOrientedUpper ε A p j) := by
  rw [annularUpperRetainedPrefixApproximationEvent,
    mem_orderedEventIntersection_ofFn_iff]
  constructor
  · intro hx j hj
    have hjmem := hx j
    simpa [annularUpperRetainedPrefixApproximationCoordinateEvent, hj]
      using! hjmem
  · intro hx j
    by_cases hj :
        annularUpperRetainedTimes p j ≤
          annularUpperRetainedSplitDepth p
    · simpa [annularUpperRetainedPrefixApproximationCoordinateEvent, hj]
        using! hx j hj
    · simp [annularUpperRetainedPrefixApproximationCoordinateEvent, hj]

theorem measurableSet_annularUpperRetainedPrefixApproximationEvent
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    MeasurableSet
      (annularUpperRetainedPrefixApproximationEvent ε A p) := by
  unfold annularUpperRetainedPrefixApproximationEvent
  apply measurableSet_orderedEventIntersection
  intro E hE
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hE
  unfold annularUpperRetainedPrefixApproximationCoordinateEvent
  split
  · exact measurableSet_gaussApproximationWindow _ _ _ _
  · exact MeasurableSet.univ

/-- Membership in the packaged masked event, with the Boolean mask
eliminated in favor of the midpoint inequality. -/
theorem mem_annularUpperRetainedMaskedApproximationDigitEvent_iff
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (x : ℝ) :
    x ∈ annularUpperRetainedMaskedApproximationDigitEvent
        ε A N p.1 (mode p.1) (hmode p.1)
        (annularUpperRetainedTimes p) ↔
      ∀ j : Fin (MixedOccurrenceCount k),
        x ∈
          if annularUpperRetainedSplitDepth p <
              annularUpperRetainedTimes p j then
            gaussDigitWindowAt
            (Real.log (N : ℝ))
            (annularUpperRetainedTimes p j)
            (annularUpperRetainedOrientedLower ε A p j)
            (annularUpperRetainedOrientedUpper ε A p j)
          else
            gaussApproximationWindow
            (Real.log (N : ℝ))
            (annularUpperRetainedTimes p j)
            (annularUpperRetainedOrientedLower ε A p j)
            (annularUpperRetainedOrientedUpper ε A p j) := by
  unfold annularUpperRetainedMaskedApproximationDigitEvent
    maskedOrderedEventIntersection
  rw [mem_orderedEventIntersection_ofFn_iff]
  constructor <;> intro hx j
  · by_cases hj :
        annularUpperRetainedSplitDepth p <
          annularUpperRetainedTimes p j
    · simpa [maskedCoordinateEvent, annularUpperRetainedFutureMask,
        annularUpperRetainedSplitDepth, annularUpperRetainedTimes,
        annularUpperRetainedOrientedLower,
        annularUpperRetainedOrientedUpper, hj]
        using! hx j
    · simpa [maskedCoordinateEvent, annularUpperRetainedFutureMask,
        annularUpperRetainedSplitDepth, annularUpperRetainedTimes,
        annularUpperRetainedOrientedLower,
        annularUpperRetainedOrientedUpper, hj]
        using! hx j
  · by_cases hj :
        annularUpperRetainedSplitDepth p <
          annularUpperRetainedTimes p j
    · simpa [maskedCoordinateEvent, annularUpperRetainedFutureMask,
        annularUpperRetainedSplitDepth, annularUpperRetainedTimes,
        annularUpperRetainedOrientedLower,
        annularUpperRetainedOrientedUpper, hj]
        using! hx j
    · simpa [maskedCoordinateEvent, annularUpperRetainedFutureMask,
        annularUpperRetainedSplitDepth, annularUpperRetainedTimes,
        annularUpperRetainedOrientedLower,
        annularUpperRetainedOrientedUpper, hj]
        using! hx j

/-- The all-exact heterogeneous tuple is exactly the intersection of its
prefix and future exact pieces. -/
theorem
    annularUpperRetained_exactTupleEvent_eq_prefix_inter_futureApproximation
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    gaussHeterogeneousApproximationTupleEvent
        (Real.log (N : ℝ))
        (annularUpperRetainedOrientedLower ε A p)
        (annularUpperRetainedOrientedUpper ε A p)
        (annularUpperRetainedTimes p) =
      annularUpperRetainedPrefixApproximationEvent ε A p ∩
        annularUpperRetainedFutureApproximationEvent ε A p := by
  ext x
  simp only [gaussHeterogeneousApproximationTupleEvent,
    annularUpperRetainedPrefixApproximationEvent,
    annularUpperRetainedFutureApproximationEvent,
    mem_orderedEventIntersection_ofFn_iff, mem_inter_iff]
  constructor
  · intro hx
    constructor
    · intro j
      unfold annularUpperRetainedPrefixApproximationCoordinateEvent
      split
      · exact hx j
      · exact Set.mem_univ x
    · intro j
      unfold annularUpperRetainedFutureApproximationCoordinateEvent
      split
      · exact hx j
      · exact Set.mem_univ x
  · rintro ⟨hprefix, hfuture⟩ j
    by_cases hj :
        annularUpperRetainedTimes p j ≤
          annularUpperRetainedSplitDepth p
    · have hjmem := hprefix j
      simpa only [
        annularUpperRetainedPrefixApproximationCoordinateEvent,
        if_pos hj] using! hjmem
    · have hjlt :
          annularUpperRetainedSplitDepth p <
            annularUpperRetainedTimes p j :=
        Nat.lt_of_not_ge hj
      have hjmem := hfuture j
      simpa only [
        annularUpperRetainedFutureApproximationCoordinateEvent,
        if_pos hjlt] using! hjmem

/-- The exact prefix event forces the initial state to lie in `(0,1]`.
The last nonzero Fourier coordinate supplies a genuine prefix coordinate,
so this fact does not rely on a future-only window. -/
theorem annularUpperRetained_prefixApproximationEvent_subset_Ioc
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N) :
    annularUpperRetainedPrefixApproximationEvent ε A p ⊆
      Ioc (0 : ℝ) 1 := by
  intro x hx
  let s :=
    annularLastNonzeroIndex (mode p.1) (hmode p.1)
  have hs :
      annularUpperRetainedTimes p s ≤
        annularUpperRetainedSplitDepth p :=
    annularUpperRetained_centerDepth_le_split hgrid htime p hN
  have hxs :
      x ∈ annularUpperRetainedPrefixApproximationCoordinateEvent
        ε A p s := by
    exact
      (mem_orderedEventIntersection_ofFn_iff.mp hx) s
  rw [annularUpperRetainedPrefixApproximationCoordinateEvent,
    if_pos hs] at hxs
  exact hxs.1

/-- The coordinatewise masked event is literally the exact prefix event
intersected with the packaged future digit block.  The apparent extra
`Ioc (0,1]` in `gaussDigitWindowAt` is redundant because the nonempty
prefix event already imposes it. -/
theorem
    annularUpperRetained_maskedEvent_eq_prefix_inter_futureDigit
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    annularUpperRetainedMaskedApproximationDigitEvent
        ε A N p.1 (mode p.1) (hmode p.1)
        (annularUpperRetainedTimes p) =
      annularUpperRetainedPrefixApproximationEvent ε A p ∩
        annularUpperRetainedFutureDigitTupleEvent ε A p := by
  ext x
  constructor
  · intro hx
    have hxMasked :=
      (mem_annularUpperRetainedMaskedApproximationDigitEvent_iff
        (ε := ε) (A := A) p x).mp hx
    constructor
    · rw [mem_annularUpperRetainedPrefixApproximationEvent_iff p x]
      intro j hj
      have hjNot :
          ¬annularUpperRetainedSplitDepth p <
            annularUpperRetainedTimes p j :=
        Nat.not_lt.mpr hj
      simpa [hjNot] using! hxMasked j
    · rw [mem_annularUpperRetainedFutureDigitTupleEvent_iff
        hgrid htime p hN hW x]
      intro j hj
      have hjmem := hxMasked j
      simp only [if_pos hj, gaussDigitWindowAt, Set.mem_inter_iff,
        Set.mem_preimage] at hjmem
      exact hjmem.2
  · rintro ⟨hprefix, hfuture⟩
    have hxIoc : x ∈ Ioc (0 : ℝ) 1 :=
      annularUpperRetained_prefixApproximationEvent_subset_Ioc
        hgrid htime p hN hprefix
    rw [mem_annularUpperRetainedMaskedApproximationDigitEvent_iff p x]
    intro j
    by_cases hj :
        annularUpperRetainedSplitDepth p <
          annularUpperRetainedTimes p j
    · have hjfuture :=
        (mem_annularUpperRetainedFutureDigitTupleEvent_iff
          hgrid htime p hN hW x).mp hfuture j hj
      simp only [if_pos hj, gaussDigitWindowAt, Set.mem_inter_iff,
        Set.mem_preimage]
      exact ⟨hxIoc, hjfuture⟩
    · have hjle :
          annularUpperRetainedTimes p j ≤
            annularUpperRetainedSplitDepth p :=
        Nat.le_of_not_gt hj
      have hjprefix :=
        (mem_annularUpperRetainedPrefixApproximationEvent_iff p x).mp
          hprefix j hjle
      simpa [hj] using! hjprefix

/-! ## A generic phase-weighted symmetric-difference bound -/

/-- Multiplying two event indicators by the same measurable unit-bounded
carrier costs at most the measure of their symmetric difference. -/
theorem norm_integral_mul_eventIndicator_sub_le_symmDiff
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (carrier : Ω → ℂ) (hcarrier : Measurable carrier)
    (hcarrierNorm : ∀ x, ‖carrier x‖ ≤ 1)
    (E D : Set Ω) (hE : MeasurableSet E) (hD : MeasurableSet D) :
    ‖(∫ x, carrier x * E.indicator (fun _ ↦ (1 : ℂ)) x ∂mu) -
        ∫ x, carrier x * D.indicator (fun _ ↦ (1 : ℂ)) x ∂mu‖ ≤
      mu.real (E ∆ D) := by
  let f : Ω → ℂ := fun x ↦
    carrier x * E.indicator (fun _ ↦ (1 : ℂ)) x
  let g : Ω → ℂ := fun x ↦
    carrier x * D.indicator (fun _ ↦ (1 : ℂ)) x
  have hfMeas : Measurable f :=
    hcarrier.mul (Measurable.ite hE measurable_const measurable_const)
  have hgMeas : Measurable g :=
    hcarrier.mul (Measurable.ite hD measurable_const measurable_const)
  have hfInt : Integrable f mu := by
    apply Integrable.of_bound hfMeas.aestronglyMeasurable 1
    filter_upwards with x
    dsimp only [f]
    rw [norm_mul]
    calc
      ‖carrier x‖ *
          ‖E.indicator (fun _ ↦ (1 : ℂ)) x‖ ≤
        1 * ‖E.indicator (fun _ ↦ (1 : ℂ)) x‖ :=
          mul_le_mul_of_nonneg_right (hcarrierNorm x) (norm_nonneg _)
      _ ≤ 1 := by
        by_cases hx : x ∈ E <;> simp [Set.indicator, hx]
  have hgInt : Integrable g mu := by
    apply Integrable.of_bound hgMeas.aestronglyMeasurable 1
    filter_upwards with x
    dsimp only [g]
    rw [norm_mul]
    calc
      ‖carrier x‖ *
          ‖D.indicator (fun _ ↦ (1 : ℂ)) x‖ ≤
        1 * ‖D.indicator (fun _ ↦ (1 : ℂ)) x‖ :=
          mul_le_mul_of_nonneg_right (hcarrierNorm x) (norm_nonneg _)
      _ ≤ 1 := by
        by_cases hx : x ∈ D <;> simp [Set.indicator, hx]
  have hsymm : MeasurableSet (E ∆ D) := hE.symmDiff hD
  rw [← integral_sub hfInt hgInt]
  calc
    ‖∫ x, f x - g x ∂mu‖ ≤
        ∫ x, (E ∆ D).indicator (fun _ ↦ (1 : ℝ)) x ∂mu := by
      apply norm_integral_le_of_norm_le
        ((integrable_const (1 : ℝ)).indicator hsymm)
      filter_upwards with x
      dsimp only [f, g]
      by_cases hxE : x ∈ E <;>
        by_cases hxD : x ∈ D <;>
          simp [Set.indicator, hxE, hxD, hcarrierNorm x,
            Set.mem_symmDiff]
    _ = mu.real (E ∆ D) := by
      exact integral_indicator_one hsymm

end

end Erdos1002
