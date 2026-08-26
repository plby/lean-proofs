import ErdosProblems.Erdos1002.GaussPrefixAnnularLateRealization
import ErdosProblems.Erdos1002.GaussPrefixAnnularRetainedGapGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Future digit blocks for upper retained annular tuples

For an upper retained chronological tuple, the midpoint construction gives
a deterministic split `m` and a gap `g`.  This file packages all coordinates
strictly after `m` as one finite digit block based at `m + g`.

The full chronological index type is retained.  Coordinates at or before the
split are assigned the event `Set.univ` and the artificial time `m + g`;
coordinates after the split keep their actual time and their parity-oriented
one-digit window.  Thus every packaged time is at least the future base, while
the package is literally the intersection of precisely the post-split digit
constraints.

We also record the corresponding exact signed-approximation event.  The
canonical parity theorem identifies it with the intersection of the
parity-oriented positive approximation windows.  This is the exact form
needed by the heterogeneous exact-to-digit replacement lemmas.
-/

open Finset MeasureTheory Set
open scoped BigOperators symmDiff

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularLateFutureBlockPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

variable {rho ε A : ℝ} {N grid : ℕ}
variable {k : AnnularGridIndex grid → ℕ}
variable {hr : 0 < MixedOccurrenceCount k}
variable
  {mode :
    (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      Fin (MixedOccurrenceCount k) → ℤ}
variable {hmode : ∀ e, mode e ≠ 0}

/-- The deterministic future base `m + g` attached to an upper retained
tuple. -/
def annularUpperRetainedFutureBase
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) : ℕ :=
  annularUpperRetainedSplitDepth p + annularUpperRetainedGap rho N

/-- The positive lower endpoint obtained from the signed annular cell and
its canonical prescribed parity. -/
def annularUpperRetainedOrientedLower
    (ε A : ℝ)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  gaussPrescribedParityOrientedLower
    (flattenedAnnularParity p.1)
    (flattenedAnnularSignedLower ε A p.1)
    (flattenedAnnularSignedUpper ε A p.1) j

/-- The positive upper endpoint obtained from the signed annular cell and
its canonical prescribed parity. -/
def annularUpperRetainedOrientedUpper
    (ε A : ℝ)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  gaussPrescribedParityOrientedUpper
    (flattenedAnnularParity p.1)
    (flattenedAnnularSignedLower ε A p.1)
    (flattenedAnnularSignedUpper ε A p.1) j

/-- Every chronological coordinate is moved, if necessary, to the future
base.  A genuinely future coordinate will be proved to remain at its actual
time. -/
def annularUpperRetainedFutureTime
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) : ℕ :=
  max (annularUpperRetainedFutureBase p)
    (annularUpperRetainedTimes p j)

/-- One base event in the future digit block.  Prefix coordinates impose no
condition; genuinely future coordinates impose their positive, parity-
oriented one-digit window. -/
def annularUpperRetainedFutureDigitEvent
    (ε A : ℝ)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) : Set ℝ :=
  if annularUpperRetainedSplitDepth p <
      annularUpperRetainedTimes p j then
    scaledGaussFirstDigitWindow
      (Real.log (N : ℝ))
      (annularUpperRetainedOrientedLower ε A p j)
      (annularUpperRetainedOrientedUpper ε A p j)
  else Set.univ

/-- One digit-surrogate coordinate event on the original Gauss state. -/
def annularUpperRetainedFutureDigitCoordinateEvent
    (ε A : ℝ)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) : Set ℝ :=
  (gaussOrbit (annularUpperRetainedFutureTime p j)) ⁻¹'
    annularUpperRetainedFutureDigitEvent ε A p j

/-- The full digit surrogate event, written directly at the packaged times. -/
def annularUpperRetainedFutureDigitTupleEvent
    (ε A : ℝ)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun j ↦
    annularUpperRetainedFutureDigitCoordinateEvent ε A p j

/-- The same future digit event in the shifted-tail representation used by
functional prefix--future mixing. -/
def annularUpperRetainedFutureDigitBlock
    (ε A : ℝ)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (x : ℝ) : ℂ :=
  gaussFutureDigitBlockIndicator
    (annularUpperRetainedFutureBase p)
    (annularUpperRetainedFutureTime p)
    (annularUpperRetainedFutureDigitEvent ε A p) x

/-- Exact positive approximation-window coordinate event.  Prefix
coordinates are again represented by `Set.univ`. -/
def annularUpperRetainedFutureApproximationCoordinateEvent
    (ε A : ℝ)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) : Set ℝ :=
  if annularUpperRetainedSplitDepth p <
      annularUpperRetainedTimes p j then
    gaussApproximationWindow
      (Real.log (N : ℝ))
      (annularUpperRetainedTimes p j)
      (annularUpperRetainedOrientedLower ε A p j)
      (annularUpperRetainedOrientedUpper ε A p j)
  else Set.univ

/-- Finite intersection of the exact positive approximation windows after
the split. -/
def annularUpperRetainedFutureApproximationEvent
    (ε A : ℝ)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun j ↦
    annularUpperRetainedFutureApproximationCoordinateEvent ε A p j

/-- The literal signed-value event after the split.  This is stated before
parity orientation and therefore exactly matches the signed value
coordinate of the marked Gauss prefix. -/
def annularUpperRetainedFutureSignedValueEvent
    (ε A : ℝ)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) : Set ℝ :=
  {x | ∀ j : Fin (MixedOccurrenceCount k),
    annularUpperRetainedSplitDepth p <
        annularUpperRetainedTimes p j →
      x ∈ gaussSignedApproximationWindow
        (Real.log (N : ℝ))
        (annularUpperRetainedTimes p j)
        (flattenedAnnularSignedLower ε A p.1 j)
        (flattenedAnnularSignedUpper ε A p.1 j)}

/-! ## Deterministic time and event facts -/

theorem annularUpperRetainedFutureBase_le_time
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) :
    annularUpperRetainedFutureBase p ≤
      annularUpperRetainedFutureTime p j := by
  exact Nat.le_max_left _ _

theorem annularUpperRetainedFutureTime_eq_base_of_le_split
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    {j : Fin (MixedOccurrenceCount k)}
    (hj : annularUpperRetainedTimes p j ≤
      annularUpperRetainedSplitDepth p) :
    annularUpperRetainedFutureTime p j =
      annularUpperRetainedFutureBase p := by
  unfold annularUpperRetainedFutureTime
  rw [Nat.max_eq_left]
  exact hj.trans (Nat.le_add_right _ _)

theorem annularUpperRetainedFutureTime_eq_actual
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    {j : Fin (MixedOccurrenceCount k)}
    (hj : annularUpperRetainedSplitDepth p <
      annularUpperRetainedTimes p j) :
    annularUpperRetainedFutureTime p j =
      annularUpperRetainedTimes p j := by
  have hbase :
      annularUpperRetainedFutureBase p ≤
        annularUpperRetainedTimes p j := by
    exact
      (annularUpperRetainedRealization_gap_package
        hgrid htime p hN hW).2.1 j hj
  exact Nat.max_eq_right hbase

@[simp] theorem annularUpperRetainedFutureDigitEvent_of_le_split
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    {j : Fin (MixedOccurrenceCount k)}
    (hj : annularUpperRetainedTimes p j ≤
      annularUpperRetainedSplitDepth p) :
    annularUpperRetainedFutureDigitEvent ε A p j = Set.univ := by
  unfold annularUpperRetainedFutureDigitEvent
  rw [if_neg (Nat.not_lt.mpr hj)]

@[simp] theorem annularUpperRetainedFutureDigitEvent_of_after_split
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    {j : Fin (MixedOccurrenceCount k)}
    (hj : annularUpperRetainedSplitDepth p <
      annularUpperRetainedTimes p j) :
    annularUpperRetainedFutureDigitEvent ε A p j =
      scaledGaussFirstDigitWindow
        (Real.log (N : ℝ))
        (annularUpperRetainedOrientedLower ε A p j)
        (annularUpperRetainedOrientedUpper ε A p j) := by
  unfold annularUpperRetainedFutureDigitEvent
  rw [if_pos hj]

@[simp] theorem
    annularUpperRetainedFutureApproximationCoordinateEvent_of_le_split
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    {j : Fin (MixedOccurrenceCount k)}
    (hj : annularUpperRetainedTimes p j ≤
      annularUpperRetainedSplitDepth p) :
    annularUpperRetainedFutureApproximationCoordinateEvent ε A p j =
      Set.univ := by
  unfold annularUpperRetainedFutureApproximationCoordinateEvent
  rw [if_neg (Nat.not_lt.mpr hj)]

@[simp] theorem
    annularUpperRetainedFutureApproximationCoordinateEvent_of_after_split
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    {j : Fin (MixedOccurrenceCount k)}
    (hj : annularUpperRetainedSplitDepth p <
      annularUpperRetainedTimes p j) :
    annularUpperRetainedFutureApproximationCoordinateEvent ε A p j =
      gaussApproximationWindow
        (Real.log (N : ℝ))
        (annularUpperRetainedTimes p j)
        (annularUpperRetainedOrientedLower ε A p j)
        (annularUpperRetainedOrientedUpper ε A p j) := by
  unfold annularUpperRetainedFutureApproximationCoordinateEvent
  rw [if_pos hj]

/-! ## Measurability -/

theorem measurableSet_annularUpperRetainedFutureDigitEvent
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) :
    MeasurableSet
      (annularUpperRetainedFutureDigitEvent ε A p j) := by
  unfold annularUpperRetainedFutureDigitEvent
  split
  · exact measurableSet_scaledGaussFirstDigitWindow _ _ _
  · exact MeasurableSet.univ

theorem measurableSet_annularUpperRetainedFutureDigitTupleEvent
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    MeasurableSet
      (annularUpperRetainedFutureDigitTupleEvent ε A p) := by
  unfold annularUpperRetainedFutureDigitTupleEvent
  apply measurableSet_orderedEventIntersection
  intro E hE
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hE
  exact
    (measurableSet_annularUpperRetainedFutureDigitEvent p j).preimage
      (measurable_gaussOrbit _)

theorem measurableSet_annularUpperRetainedFutureDigitCoordinateEvent
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) :
    MeasurableSet
      (annularUpperRetainedFutureDigitCoordinateEvent ε A p j) := by
  exact
    (measurableSet_annularUpperRetainedFutureDigitEvent p j).preimage
      (measurable_gaussOrbit _)

theorem measurable_annularUpperRetainedFutureDigitBlock_future
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    @Measurable ℝ ℂ
      (gaussFutureMeasurableSpace
        (annularUpperRetainedFutureBase p))
      (borel ℂ)
      (annularUpperRetainedFutureDigitBlock ε A p) := by
  exact measurable_gaussFutureDigitBlockIndicator_future
    (annularUpperRetainedFutureBase p)
    (annularUpperRetainedFutureTime p)
    (measurableSet_annularUpperRetainedFutureDigitEvent p)

theorem
    measurableSet_annularUpperRetainedFutureApproximationCoordinateEvent
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) :
    MeasurableSet
      (annularUpperRetainedFutureApproximationCoordinateEvent ε A p j) := by
  unfold annularUpperRetainedFutureApproximationCoordinateEvent
  split
  · exact measurableSet_gaussApproximationWindow _ _ _ _
  · exact MeasurableSet.univ

theorem measurableSet_annularUpperRetainedFutureApproximationEvent
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    MeasurableSet
      (annularUpperRetainedFutureApproximationEvent ε A p) := by
  unfold annularUpperRetainedFutureApproximationEvent
  apply measurableSet_orderedEventIntersection
  intro E hE
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hE
  exact
    measurableSet_annularUpperRetainedFutureApproximationCoordinateEvent p j

theorem measurableSet_annularUpperRetainedFutureSignedValueEvent
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    MeasurableSet
      (annularUpperRetainedFutureSignedValueEvent ε A p) := by
  have heq :
      annularUpperRetainedFutureSignedValueEvent ε A p =
        ⋂ j : Fin (MixedOccurrenceCount k),
          if annularUpperRetainedSplitDepth p <
              annularUpperRetainedTimes p j then
            gaussSignedApproximationWindow
              (Real.log (N : ℝ))
              (annularUpperRetainedTimes p j)
              (flattenedAnnularSignedLower ε A p.1 j)
              (flattenedAnnularSignedUpper ε A p.1 j)
          else Set.univ := by
    ext x
    simp only [annularUpperRetainedFutureSignedValueEvent,
      Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hx j
      by_cases hj : annularUpperRetainedSplitDepth p <
          annularUpperRetainedTimes p j
      · simpa only [if_pos hj] using! hx j hj
      · simp only [if_neg hj, Set.mem_univ]
    · intro hx j hj
      simpa only [if_pos hj] using! hx j
  rw [heq]
  apply MeasurableSet.iInter
  intro j
  split
  · exact measurableSet_gaussSignedApproximationWindow _ _ _ _
  · exact MeasurableSet.univ

/-! ## Exact set and indicator identities -/

/-- Pulling the shifted future block back to the original Gauss state gives
the directly written digit tuple event. -/
theorem annularUpperRetainedFutureDigitBlock_preimage_eq
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    (gaussOrbit (annularUpperRetainedFutureBase p)) ⁻¹'
        shiftedGaussTailEvent
          (annularUpperRetainedFutureBase p)
          (annularUpperRetainedFutureTime p)
          (annularUpperRetainedFutureDigitEvent ε A p) =
      annularUpperRetainedFutureDigitTupleEvent ε A p := by
  simpa only [annularUpperRetainedFutureDigitTupleEvent] using!
    shiftedGaussTailEvent_preimage
      (fun j ↦ annularUpperRetainedFutureBase_le_time p j)

/-- The packaged future block is literally the complex indicator of the
direct future digit tuple event. -/
theorem annularUpperRetainedFutureDigitBlock_eq_eventIndicator
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (x : ℝ) :
    annularUpperRetainedFutureDigitBlock ε A p x =
      (annularUpperRetainedFutureDigitTupleEvent ε A p).indicator
        (fun _ ↦ (1 : ℂ)) x := by
  unfold annularUpperRetainedFutureDigitBlock
    gaussFutureDigitBlockIndicator
  rw [annularUpperRetainedFutureDigitBlock_preimage_eq p]

/-- Exact membership description: only indices genuinely after the split
impose a digit condition, and they do so at their original chronological
time. -/
theorem mem_annularUpperRetainedFutureDigitTupleEvent_iff
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (x : ℝ) :
    x ∈ annularUpperRetainedFutureDigitTupleEvent ε A p ↔
      ∀ j : Fin (MixedOccurrenceCount k),
        annularUpperRetainedSplitDepth p <
            annularUpperRetainedTimes p j →
          gaussOrbit (annularUpperRetainedTimes p j) x ∈
            scaledGaussFirstDigitWindow
              (Real.log (N : ℝ))
              (annularUpperRetainedOrientedLower ε A p j)
              (annularUpperRetainedOrientedUpper ε A p j) := by
  simp only [annularUpperRetainedFutureDigitTupleEvent,
    mem_orderedEventIntersection_ofFn_iff,
    annularUpperRetainedFutureDigitCoordinateEvent, Set.mem_preimage]
  constructor
  · intro hx j hj
    have hjmem := hx j
    rw [annularUpperRetainedFutureTime_eq_actual
      hgrid htime p hN hW hj,
      annularUpperRetainedFutureDigitEvent_of_after_split p hj] at hjmem
    exact hjmem
  · intro hx j
    by_cases hj : annularUpperRetainedSplitDepth p <
        annularUpperRetainedTimes p j
    · rw [annularUpperRetainedFutureTime_eq_actual
        hgrid htime p hN hW hj,
        annularUpperRetainedFutureDigitEvent_of_after_split p hj]
      exact hx j hj
    · have hjle : annularUpperRetainedTimes p j ≤
          annularUpperRetainedSplitDepth p := Nat.le_of_not_gt hj
      rw [annularUpperRetainedFutureTime_eq_base_of_le_split p hjle,
        annularUpperRetainedFutureDigitEvent_of_le_split p hjle]
      exact Set.mem_univ _

/-- The future block indicator is the finite product of its coordinate
indicators. -/
theorem annularUpperRetainedFutureDigitBlock_eq_prod
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (x : ℝ) :
    annularUpperRetainedFutureDigitBlock ε A p x =
      ∏ j : Fin (MixedOccurrenceCount k),
        ((annularUpperRetainedFutureDigitCoordinateEvent ε A p j).indicator
          (fun _ ↦ (1 : ℂ)) x) := by
  rw [annularUpperRetainedFutureDigitBlock_eq_eventIndicator]
  classical
  by_cases hall : ∀ j : Fin (MixedOccurrenceCount k),
      x ∈ annularUpperRetainedFutureDigitCoordinateEvent ε A p j
  · have hx :
      x ∈ annularUpperRetainedFutureDigitTupleEvent ε A p := by
      exact mem_orderedEventIntersection_ofFn_iff.mpr hall
    rw [Set.indicator_of_mem hx]
    symm
    apply Finset.prod_eq_one
    intro j _hj
    rw [Set.indicator_of_mem (hall j)]
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    have hx :
        x ∉ annularUpperRetainedFutureDigitTupleEvent ε A p := by
      intro hx
      exact hj (mem_orderedEventIntersection_ofFn_iff.mp hx j)
    rw [Set.indicator_of_notMem hx]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [Set.indicator_of_notMem hj]

/-- Expanded product identity with all prefix coordinates literally equal
to `1` and every genuine future coordinate evaluated at its original
chronological time. -/
theorem annularUpperRetainedFutureDigitBlock_eq_postSplit_prod
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (x : ℝ) :
    annularUpperRetainedFutureDigitBlock ε A p x =
      ∏ j : Fin (MixedOccurrenceCount k),
        if annularUpperRetainedSplitDepth p <
            annularUpperRetainedTimes p j then
          (((gaussOrbit (annularUpperRetainedTimes p j)) ⁻¹'
              scaledGaussFirstDigitWindow
                (Real.log (N : ℝ))
                (annularUpperRetainedOrientedLower ε A p j)
                (annularUpperRetainedOrientedUpper ε A p j)).indicator
            (fun _ ↦ (1 : ℂ)) x)
        else 1 := by
  rw [annularUpperRetainedFutureDigitBlock_eq_prod]
  apply Finset.prod_congr rfl
  intro j _hj
  by_cases hj : annularUpperRetainedSplitDepth p <
      annularUpperRetainedTimes p j
  · rw [if_pos hj]
    unfold annularUpperRetainedFutureDigitCoordinateEvent
    rw [annularUpperRetainedFutureTime_eq_actual
      hgrid htime p hN hW hj,
      annularUpperRetainedFutureDigitEvent_of_after_split p hj]
  · rw [if_neg hj]
    have hjle : annularUpperRetainedTimes p j ≤
        annularUpperRetainedSplitDepth p := Nat.le_of_not_gt hj
    unfold annularUpperRetainedFutureDigitCoordinateEvent
    rw [annularUpperRetainedFutureDigitEvent_of_le_split p hjle]
    simp

/-- Canonical annular membership fixes the actual depth parity to the
prescribed parity used in the positive endpoints. -/
theorem annularUpperRetained_actual_orientedLower_eq
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) :
    gaussParityOrientedLower
        (annularUpperRetainedTimes p j)
        (flattenedAnnularSignedLower ε A p.1 j)
        (flattenedAnnularSignedUpper ε A p.1 j) =
      annularUpperRetainedOrientedLower ε A p j := by
  unfold annularUpperRetainedOrientedLower
    gaussPrescribedParityOrientedLower
  apply gaussParityOrientedLower_eq_of_mod_two_eq
  have hparity :=
    canonicalAnnularGridTupleFamily_parity
      N k p.1 (annularUpperRetainedTimes p)
      (annularUpperRetainedTimes_mem_canonical p) j
  rw [Nat.mod_eq_of_lt (flattenedAnnularParity p.1 j).isLt]
  exact hparity

theorem annularUpperRetained_actual_orientedUpper_eq
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) :
    gaussParityOrientedUpper
        (annularUpperRetainedTimes p j)
        (flattenedAnnularSignedLower ε A p.1 j)
        (flattenedAnnularSignedUpper ε A p.1 j) =
      annularUpperRetainedOrientedUpper ε A p j := by
  unfold annularUpperRetainedOrientedUpper
    gaussPrescribedParityOrientedUpper
  apply gaussParityOrientedUpper_eq_of_mod_two_eq
  have hparity :=
    canonicalAnnularGridTupleFamily_parity
      N k p.1 (annularUpperRetainedTimes p)
      (annularUpperRetainedTimes_mem_canonical p) j
  rw [Nat.mod_eq_of_lt (flattenedAnnularParity p.1 j).isLt]
  exact hparity

/-- The literal post-split signed-value constraints are exactly the
post-split parity-oriented positive approximation windows. -/
theorem annularUpperRetainedFutureSignedValueEvent_eq_approximationEvent
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    annularUpperRetainedFutureSignedValueEvent ε A p =
      annularUpperRetainedFutureApproximationEvent ε A p := by
  ext x
  simp only [annularUpperRetainedFutureSignedValueEvent,
    Set.mem_setOf_eq, annularUpperRetainedFutureApproximationEvent,
    mem_orderedEventIntersection_ofFn_iff]
  constructor
  · intro hx j
    by_cases hj : annularUpperRetainedSplitDepth p <
        annularUpperRetainedTimes p j
    · rw [
        annularUpperRetainedFutureApproximationCoordinateEvent_of_after_split
          p hj,
        ← annularUpperRetained_actual_orientedLower_eq (ε := ε) (A := A) p j,
        ← annularUpperRetained_actual_orientedUpper_eq (ε := ε) (A := A) p j,
        ← gaussSignedApproximationWindow_eq_oriented]
      exact hx j hj
    · have hjle : annularUpperRetainedTimes p j ≤
          annularUpperRetainedSplitDepth p := Nat.le_of_not_gt hj
      rw [
        annularUpperRetainedFutureApproximationCoordinateEvent_of_le_split
          p hjle]
      exact Set.mem_univ _
  · intro hx j hj
    have hjmem := hx j
    rw [
      annularUpperRetainedFutureApproximationCoordinateEvent_of_after_split
        p hj,
      ← annularUpperRetained_actual_orientedLower_eq (ε := ε) (A := A) p j,
      ← annularUpperRetained_actual_orientedUpper_eq (ε := ε) (A := A) p j,
      ← gaussSignedApproximationWindow_eq_oriented] at hjmem
    exact hjmem

/-- The future digit tuple is exactly the coordinate-wise digit surrogate
of the positive approximation event.  This bridge leaves the symmetric
difference in the generic form consumed by
`symmDiff_orderedIntersections_subset_iUnion_witness`. -/
theorem annularUpperRetainedFutureDigitTupleEvent_eq_coordinateSurrogate
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    annularUpperRetainedFutureDigitTupleEvent ε A p =
      orderedEventIntersection (List.ofFn fun j ↦
        if annularUpperRetainedSplitDepth p <
            annularUpperRetainedTimes p j then
          (gaussOrbit (annularUpperRetainedTimes p j)) ⁻¹'
            scaledGaussFirstDigitWindow
              (Real.log (N : ℝ))
              (annularUpperRetainedOrientedLower ε A p j)
              (annularUpperRetainedOrientedUpper ε A p j)
        else Set.univ) := by
  ext x
  simp only [annularUpperRetainedFutureDigitTupleEvent,
    mem_orderedEventIntersection_ofFn_iff,
    annularUpperRetainedFutureDigitCoordinateEvent, Set.mem_preimage]
  constructor
  · intro hx j
    by_cases hj : annularUpperRetainedSplitDepth p <
        annularUpperRetainedTimes p j
    · rw [if_pos hj]
      have hjmem := hx j
      rw [annularUpperRetainedFutureTime_eq_actual
        hgrid htime p hN hW hj,
        annularUpperRetainedFutureDigitEvent_of_after_split p hj] at hjmem
      exact hjmem
    · rw [if_neg hj]
      exact Set.mem_univ _
  · intro hx j
    by_cases hj : annularUpperRetainedSplitDepth p <
        annularUpperRetainedTimes p j
    · have hjmem := hx j
      rw [if_pos hj] at hjmem
      rw [annularUpperRetainedFutureTime_eq_actual
        hgrid htime p hN hW hj,
        annularUpperRetainedFutureDigitEvent_of_after_split p hj]
      exact hjmem
    · have hjle : annularUpperRetainedTimes p j ≤
          annularUpperRetainedSplitDepth p := Nat.le_of_not_gt hj
      rw [annularUpperRetainedFutureTime_eq_base_of_le_split p hjle,
        annularUpperRetainedFutureDigitEvent_of_le_split p hjle]
      exact Set.mem_univ _

/-- The generic coordinate-replacement cover applies verbatim to the exact
future approximation event and the packaged digit surrogate.  This is the
set-theoretic input for the quantitative boundary-strip estimates. -/
theorem
    symmDiff_annularUpperRetainedFutureApproximation_digit_subset_witnesses
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    annularUpperRetainedFutureApproximationEvent ε A p ∆
        annularUpperRetainedFutureDigitTupleEvent ε A p ⊆
      ⋃ j : Fin (MixedOccurrenceCount k),
        coordinateReplacementWitness
          (annularUpperRetainedFutureApproximationCoordinateEvent ε A p)
          (annularUpperRetainedFutureDigitCoordinateEvent ε A p) j := by
  unfold annularUpperRetainedFutureApproximationEvent
    annularUpperRetainedFutureDigitTupleEvent
  exact
    symmDiff_orderedIntersections_subset_iUnion_witness
      (annularUpperRetainedFutureApproximationCoordinateEvent ε A p)
      (annularUpperRetainedFutureDigitCoordinateEvent ε A p)

/-- Signed-value version of the same replacement cover. -/
theorem
    symmDiff_annularUpperRetainedFutureSignedValue_digit_subset_witnesses
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    annularUpperRetainedFutureSignedValueEvent ε A p ∆
        annularUpperRetainedFutureDigitTupleEvent ε A p ⊆
      ⋃ j : Fin (MixedOccurrenceCount k),
        coordinateReplacementWitness
          (annularUpperRetainedFutureApproximationCoordinateEvent ε A p)
          (annularUpperRetainedFutureDigitCoordinateEvent ε A p) j := by
  rw [annularUpperRetainedFutureSignedValueEvent_eq_approximationEvent]
  exact
    symmDiff_annularUpperRetainedFutureApproximation_digit_subset_witnesses p

/-! ## A genuinely nontrivial future coordinate -/

theorem exists_annularUpperRetained_genuineFutureDigitCoordinate
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    ∃ j : Fin (MixedOccurrenceCount k),
      annularUpperRetainedSplitDepth p <
          annularUpperRetainedTimes p j ∧
        annularUpperRetainedFutureTime p j =
          annularUpperRetainedTimes p j ∧
        annularUpperRetainedFutureDigitEvent ε A p j =
          scaledGaussFirstDigitWindow
            (Real.log (N : ℝ))
            (annularUpperRetainedOrientedLower ε A p j)
            (annularUpperRetainedOrientedUpper ε A p j) := by
  obtain ⟨j, hj⟩ := annularUpperRetained_exists_after_split p hW
  exact ⟨j, hj,
    annularUpperRetainedFutureTime_eq_actual
      hgrid htime p hN hW hj,
    annularUpperRetainedFutureDigitEvent_of_after_split p hj⟩

end

end Erdos1002
