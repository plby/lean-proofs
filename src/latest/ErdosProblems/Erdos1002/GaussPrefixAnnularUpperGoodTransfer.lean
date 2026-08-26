import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperContracted
import ErdosProblems.Erdos1002.GaussPrefixAnnularDelayedFreezing
import ErdosProblems.Erdos1002.GaussPrefixAnnularBadEventMoments
import ErdosProblems.Erdos1002.GaussPrefixAnnularLowerRetained

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Denominator-good transfer for contracted upper annular tuples

This file performs one finite-`N` replacement, before any prefix freezing,
future digit replacement, or mixing argument.  On a single global
denominator-good event, the exact moving marked tuple integrand agrees with
the full Gauss-prefix mixed character.  We retain the mixed character at
every selected coordinate and merely restrict it to the prefix-good event at
the delayed split

`b = m + ⌊g / 2⌋`.

The complement is controlled after summing all chronological labels and all
contracted upper tuples.  The norm remains inside the finite comparison
until the complete homogeneous approximation-window count has been exposed.
The already-proved bad-event moment estimate then makes the aggregate error
vanish.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 800000

local instance gaussPrefixAnnularUpperGoodTransferPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## Tagged contracted upper tuples and their canonical realization -/

/-- A chronological ordering together with one tuple in the contracted
upper-retained midpoint family. -/
def AnnularContractedUpperRetainedTaggedTuple
    (eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :=
  Σ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    ↥(contractedAnnularCanonicalLaterUpperMidpointTupleFamily
      eta rho N k hr e (mode e) (hmode e))

instance annularContractedUpperRetainedTaggedTupleFintype
    (eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Fintype
      (AnnularContractedUpperRetainedTaggedTuple
        eta rho N k hr mode hmode) := by
  unfold AnnularContractedUpperRetainedTaggedTuple
  infer_instance

instance annularContractedUpperRetainedTaggedTupleDecidableEq
    (eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    DecidableEq
      (AnnularContractedUpperRetainedTaggedTuple
        eta rho N k hr mode hmode) :=
  Classical.decEq _

/-- Forget the contraction proof and regard a contracted tuple as an
ordinary upper-retained tagged tuple. -/
def annularContractedUpperRetainedToUpper
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    AnnularUpperRetainedTaggedTuple rho N k hr mode hmode :=
  ⟨p.1,
    ⟨p.2.1,
      contractedAnnularCanonicalLaterUpperMidpointTupleFamily_subset_upper
        k hr p.1 (mode p.1) (hmode p.1) p.2.2⟩⟩

/-- The chronological time tuple underlying a contracted upper tag. -/
def annularContractedUpperRetainedTimes
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    Fin (MixedOccurrenceCount k) → ℕ :=
  p.2.1

@[simp] theorem annularContractedUpperRetainedTimes_embedding
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularUpperRetainedTimes
        (annularContractedUpperRetainedToUpper p) =
      annularContractedUpperRetainedTimes p := by
  change p.2.1 = p.2.1
  rfl

theorem annularContractedUpperRetainedTimes_mem_canonical
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedUpperRetainedTimes p ∈
      canonicalAnnularGridTupleFamily N k p.1 :=
  contractedAnnularCanonicalLaterUpperMidpointTupleFamily_subset_canonical
    k hr p.1 (mode p.1) (hmode p.1) p.2.2

/-- We use exactly the canonical realization already fixed for the
uncontracted upper tag.  Thus all later delayed-prefix and future-block
lemmas apply without any change of realization. -/
def annularContractedUpperRetainedRealization
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    GloballyInjectiveMixedDepthTuple N k :=
  annularUpperRetainedRealization
    (annularContractedUpperRetainedToUpper p)

@[simp] theorem annularContractedUpperRetainedRealization_embedding
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedUpperRetainedRealization p =
      annularUpperRetainedRealization
        (annularContractedUpperRetainedToUpper p) := by
  rfl

theorem annularContractedUpperRetainedRealization_times
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    fixedOrderMixedTimes N k p.1
        (annularContractedUpperRetainedRealization p) =
      annularContractedUpperRetainedTimes p := by
  simpa only [annularContractedUpperRetainedRealization,
    annularContractedUpperRetainedTimes_embedding] using!
    annularUpperRetainedRealization_times
      (annularContractedUpperRetainedToUpper p)

/-- The delayed prefix depth `b` used for the prefix-good restriction,
freezing, and subsequent prefix--future mixing. -/
def annularContractedUpperRetainedDelayedDepth
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℕ :=
  annularUpperRetainedDelayedSplitDepth
    (annularContractedUpperRetainedToUpper p)

@[simp] theorem annularContractedUpperRetainedDelayedDepth_embedding
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedUpperRetainedDelayedDepth p =
      annularUpperRetainedDelayedSplitDepth
        (annularContractedUpperRetainedToUpper p) := by
  rfl

/-- Fixed denominator tolerance for this transfer.  Its normalization by
`gaussRoofMean` makes the eventual contraction-margin calculation
transparent. -/
def upperGoodTransferDenominatorTolerance (eta rho : ℝ) : ℝ :=
  gaussRoofMean * min eta rho / 8

theorem upperGoodTransferDenominatorTolerance_pos
    {eta rho : ℝ} (heta : 0 < eta) (hrho : 0 < rho) :
    0 < upperGoodTransferDenominatorTolerance eta rho := by
  unfold upperGoodTransferDenominatorTolerance
  have hmin : 0 < min eta rho := lt_min heta hrho
  exact div_pos (mul_pos gaussRoofMean_pos hmin) (by norm_num)

/-- The transfer tolerance is smaller than the tolerance admitted by the
variable-tolerance shallow-cylinder estimate. -/
theorem upperGoodTransferDenominatorTolerance_le_rhoSixth
    {eta rho : ℝ} (hrho : 0 ≤ rho) :
    upperGoodTransferDenominatorTolerance eta rho ≤
      gaussRoofMean * rho / 6 := by
  have hmin : min eta rho ≤ rho := min_le_right _ _
  have hmu : 0 ≤ gaussRoofMean := gaussRoofMean_pos.le
  unfold upperGoodTransferDenominatorTolerance
  have hmul :
      gaussRoofMean * min eta rho ≤ gaussRoofMean * rho :=
    mul_le_mul_of_nonneg_left hmin hmu
  have hnonneg : 0 ≤ gaussRoofMean * rho :=
    mul_nonneg hmu hrho
  nlinarith

/-! ## Exact moving and prefix-good mixed-character sums -/

/-- Exact moving contribution of one contracted upper tag. -/
def annularContractedUpperRetainedMovingContribution
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  ∫ x, gaussMovingSignedMarkedTupleIntegrand
    N (Real.log (N : ℝ))
    (flattenedAnnularSignedLower ε A p.1)
    (flattenedAnnularSignedUpper ε A p.1)
    (mode p.1)
    (annularContractedUpperRetainedTimes p) x
    ∂uniform01Measure

/-- Exact moving aggregate over all chronological tags and contracted upper
tuples. -/
def annularContractedUpperRetainedMovingSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    annularContractedUpperRetainedMovingContribution
      ε A eta rho N k hr mode hmode p

/-- The full mixed character of one contracted upper tag, restricted only
to denominator goodness through its delayed depth.  No future event has
yet been replaced or frozen. -/
def annularContractedUpperRetainedPrefixGoodMixedContribution
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  ∫ x,
    (gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)).indicator
      (gaussPrefixMarkedMixedTupleCharacter N
        (fun i ↦ compactValueMarkedRegion
          (activeAnnularOccurrenceSignedLower k ε A i)
          (activeAnnularOccurrenceSignedUpper k ε A i))
        k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedUpperRetainedRealization p).1) x
    ∂uniform01Measure

/-- Aggregate of the delayed-prefix-good full mixed characters. -/
def annularContractedUpperRetainedPrefixGoodMixedSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode,
    annularContractedUpperRetainedPrefixGoodMixedContribution
      ε A eta rho N k hr mode hmode p

/-- The tagged moving aggregate is literally the nested paper-facing sum
over chronological orders and contracted upper-retained tuple families. -/
theorem annularContractedUpperRetainedMovingSum_eq_nested
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    annularContractedUpperRetainedMovingSum
        ε A eta rho N k hr mode hmode =
      ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          (mode e)
          (contractedAnnularCanonicalLaterUpperMidpointTupleFamily
            eta rho N k hr e (mode e) (hmode e)) := by
  classical
  let f := fun
      (e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (p : ↥(contractedAnnularCanonicalLaterUpperMidpointTupleFamily
        eta rho N k hr e (mode e) (hmode e))) ↦
    ∫ x, gaussMovingSignedMarkedTupleIntegrand
      N (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
      (mode e) p.1 x
      ∂uniform01Measure
  unfold annularContractedUpperRetainedMovingSum
    annularContractedUpperRetainedMovingContribution
  change
    (∑ p : Σ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ↥(contractedAnnularCanonicalLaterUpperMidpointTupleFamily
          eta rho N k hr e (mode e) (hmode e)),
      f p.1 p.2) = _
  rw [Fintype.sum_sigma']
  apply Finset.sum_congr rfl
  intro e _he
  unfold uniformMovingSignedMarkedFourierTupleSum
  rw [← Finset.attach_eq_univ
    (s := contractedAnnularCanonicalLaterUpperMidpointTupleFamily
      eta rho N k hr e (mode e) (hmode e))]
  simp only [f]
  exact Finset.sum_attach
    (contractedAnnularCanonicalLaterUpperMidpointTupleFamily
      eta rho N k hr e (mode e) (hmode e))
    (fun t ↦
      ∫ x, gaussMovingSignedMarkedTupleIntegrand
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (mode e) t x
        ∂uniform01Measure)

/-! ## Pointwise bridge and homogeneous event domination -/

/-- The prescribed parity in the canonical box is the actual parity of
every contracted upper-retained depth. -/
theorem annularContractedUpperRetainedTimes_parity
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) :
    annularContractedUpperRetainedTimes p j % 2 =
      (flattenedAnnularParity p.1 j).1 := by
  rcases mem_canonicalMixedOrderParityBoxTimes_iff.mp
      (annularContractedUpperRetainedTimes_mem_canonical p) with
    ⟨F, _horder, hboxes, htimes⟩
  have hj := (hboxes j).2
  rw [htimes] at hj
  exact hj

/-- The signed annular event for one contracted upper tuple is contained
in the homogeneous positive approximation window `[ε,A]` at every
selected depth. -/
theorem annularContractedUpperRetained_signedEvent_subset_windowEvent
    {ε A eta rho : ℝ} (hεA : ε < A)
    {N grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
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
        (annularContractedUpperRetainedTimes p) ⊆
      orderedEventIntersection
        (List.ofFn fun j ↦
          gaussApproximationWindow (Real.log (N : ℝ))
            (annularContractedUpperRetainedTimes p j) ε A) := by
  intro x hx
  have hallSigned :=
    mem_orderedEventIntersection_ofFn_iff.mp hx
  apply mem_orderedEventIntersection_ofFn_iff.mpr
  intro j
  have hj := hallSigned j
  rw [gaussSignedApproximationWindow_eq_oriented] at hj
  have hlowerEq :
      gaussParityOrientedLower
          (annularContractedUpperRetainedTimes p j)
          (flattenedAnnularSignedLower ε A p.1 j)
          (flattenedAnnularSignedUpper ε A p.1 j) =
        gaussPrescribedParityOrientedLower
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1) j := by
    apply gaussParityOrientedLower_eq_of_mod_two_eq
    rw [Nat.mod_eq_of_lt
      (flattenedAnnularParity p.1 j).isLt]
    exact annularContractedUpperRetainedTimes_parity p j
  have hupperEq :
      gaussParityOrientedUpper
          (annularContractedUpperRetainedTimes p j)
          (flattenedAnnularSignedLower ε A p.1 j)
          (flattenedAnnularSignedUpper ε A p.1 j) =
        gaussPrescribedParityOrientedUpper
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1) j := by
    apply gaussParityOrientedUpper_eq_of_mod_two_eq
    rw [Nat.mod_eq_of_lt
      (flattenedAnnularParity p.1 j).isLt]
    exact annularContractedUpperRetainedTimes_parity p j
  rw [hlowerEq, hupperEq] at hj
  rcases hj with ⟨hxUnit, hjValue⟩
  refine ⟨hxUnit, ?_⟩
  exact ⟨
    (flattenedAnnular_oriented_lower_ge_epsilon
      hεA hgrid hsigned p.1 j).trans hjValue.1,
    hjValue.2.trans
      (flattenedAnnular_oriented_upper_le
        hεA hgrid hsigned p.1 j)⟩

/-- Membership in the full mixed marked event implies membership in the
homogeneous approximation-window event.  The assertion is made only on
`(0,1]`, exactly the domain on which the marked-point data identity is
available. -/
theorem
    annularContractedUpperRetained_mixedEvent_subset_windowEvent_of_mem_Ioc
    {ε A eta rho : ℝ} (hεA : ε < A)
    {N grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    {x : ℝ} (hxIoc : x ∈ Ioc (0 : ℝ) 1)
    (hxMixed :
      x ∈ mixedTupleEvent
        (fun i ↦ gaussPrefixMarkedEvent N
          (compactValueMarkedRegion
            (activeAnnularOccurrenceSignedLower k ε A i)
            (activeAnnularOccurrenceSignedUpper k ε A i)))
        (annularContractedUpperRetainedRealization p).1) :
    x ∈ orderedEventIntersection
      (List.ofFn fun j ↦
        gaussApproximationWindow (Real.log (N : ℝ))
          (annularContractedUpperRetainedTimes p j) ε A) := by
  apply
    annularContractedUpperRetained_signedEvent_subset_windowEvent
      hεA hgrid hsigned p
  apply mem_orderedEventIntersection_ofFn_iff.mpr
  intro j
  let z : GaussPrefixMixedOccurrence k := p.1 j
  have hevent :
      x ∈ gaussPrefixMarkedEvent N
        (compactValueMarkedRegion
          (activeAnnularOccurrenceSignedLower k ε A z.1)
          (activeAnnularOccurrenceSignedUpper k ε A z.1))
        ((annularContractedUpperRetainedRealization p).1 z.1 z.2) := by
    exact Set.mem_iInter.mp
      (Set.mem_iInter.mp hxMixed z.1) z.2
  have hdata := selectedGaussPrefixWord_data_of_mem hevent
  have hactive : 0 < k z.1 := by
    have hz := z.2.isLt
    omega
  have htime :
      ((annularContractedUpperRetainedRealization p).1 z.1 z.2 : ℕ) =
        annularContractedUpperRetainedTimes p j := by
    have hj :=
      congrFun (annularContractedUpperRetainedRealization_times p) j
    simpa only [fixedOrderMixedTimes, z] using! hj
  rw [← htime]
  refine ⟨hxIoc, ?_⟩
  change
    gaussSignedScaledApproximationCoordinate
        (Real.log (N : ℝ))
        ((annularContractedUpperRetainedRealization p).1
          z.1 z.2 : ℕ) x ∈
      Icc (flattenedAnnularSignedLower ε A p.1 j)
        (flattenedAnnularSignedUpper ε A p.1 j)
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

/-- A delayed split belonging to an upper-retained tuple is strictly below
the ambient depth horizon. -/
theorem annularContractedUpperRetainedDelayedDepth_lt_ambient
    {eta rho : ℝ} {N grid : ℕ}
    (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    annularContractedUpperRetainedDelayedDepth p <
      annularDepthAmbientSize N := by
  have h :=
    annularUpperRetained_delayedSplit_add_gap_lt_ambient
      hgrid htime (annularContractedUpperRetainedToUpper p) hN hW
  exact
    (Nat.le_add_right
      (annularContractedUpperRetainedDelayedDepth p)
      (annularUpperRetainedDelayedMixingGap rho N)).trans_lt h

/-- On the global denominator-good event, the exact moving integrand is
the full mixed character restricted to prefix goodness through the delayed
depth.  Both the continued-fraction bridge and the global-to-prefix
inclusion are almost-everywhere statements, so no rational endpoint is
silently discarded. -/
theorem
    ae_annularContractedUpperRetained_moving_eq_prefixGoodMixed_on_globalGood
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
        eta * Real.log (N : ℝ))
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    ∀ᵐ x ∂uniform01Measure,
      x ∈ gaussDenominatorLinearGoodEvent 1
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho) →
        gaussMovingSignedMarkedTupleIntegrand
            N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A p.1)
            (flattenedAnnularSignedUpper ε A p.1)
            (mode p.1)
            (annularContractedUpperRetainedTimes p) x =
          (gaussDenominatorPrefixGoodEvent
            (annularContractedUpperRetainedDelayedDepth p)
            (annularDepthAmbientSize N)
            (upperGoodTransferDenominatorTolerance eta rho)).indicator
            (gaussPrefixMarkedMixedTupleCharacter N
              (fun i ↦ compactValueMarkedRegion
                (activeAnnularOccurrenceSignedLower k ε A i)
                (activeAnnularOccurrenceSignedUpper k ε A i))
              k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1) x := by
  have hcanonical :=
    annularContractedUpperRetainedTimes_mem_canonical p
  have hprefix :
      gaussDenominatorLinearGoodEvent 1
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho)
        ≤ᵐ[uniform01Measure]
      gaussDenominatorPrefixGoodEvent
          (annularContractedUpperRetainedDelayedDepth p)
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho) := by
    apply gaussDenominatorLinearGoodEvent_ae_subset_prefixGoodEvent
    simpa only [one_mul] using!
      (annularContractedUpperRetainedDelayedDepth_lt_ambient
        hgrid htime p (by omega) hW).le
  filter_upwards [ae_nonterminating_uniform01, hprefix] with
      x hxNonterm hxPrefix hxGood
  have hxPrefixGood :
      x ∈ gaussDenominatorPrefixGoodEvent
          (annularContractedUpperRetainedDelayedDepth p)
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho) :=
    hxPrefix hxGood
  have hbound :
      ∀ j,
        fixedOrderMixedTimes N k p.1
            (annularContractedUpperRetainedRealization p) j ≤
          1 * annularDepthAmbientSize N := by
    intro j
    rw [annularContractedUpperRetainedRealization_times p]
    simpa only [one_mul] using!
      (canonicalAnnularGridTupleFamily_lt_ambient
        hgrid k htime (by omega) p.1
        (annularContractedUpperRetainedTimes p) hcanonical j).le
  have hboxes :
      ∀ j,
        fixedOrderMixedTimes N k p.1
            (annularContractedUpperRetainedRealization p) j ∈
          contractedAnnularTimeDepthBox N eta (p.1 j).1 := by
    intro j
    rw [annularContractedUpperRetainedRealization_times p]
    exact
      contractedAnnularCanonicalLaterUpperMidpointTupleFamily_boxes
        p.2.2 j
  have hbridge :=
    gaussMovingAnnularMarkedTupleIntegrand_eq_mixedCharacter_of_good_contracted
      hε hεA hgrid hN k p.1
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularContractedUpperRetainedRealization p)
      htime hsigned hsmall hxNonterm.1 hxNonterm.2 hxGood
      hbound hmargin hboxes
  rw [flattenedAnnularFourierMode_unflattened,
    annularContractedUpperRetainedRealization_times p] at hbridge
  calc
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
        (annularContractedUpperRetainedRealization p).1 x :=
      hbridge.trans
        (gaussPrefixMarkedMixedTupleCharacter_activeAnnular_eq
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1 x).symm
    _ =
      (gaussDenominatorPrefixGoodEvent
        (annularContractedUpperRetainedDelayedDepth p)
        (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho)).indicator
        (gaussPrefixMarkedMixedTupleCharacter N
          (fun i ↦ compactValueMarkedRegion
            (activeAnnularOccurrenceSignedLower k ε A i)
            (activeAnnularOccurrenceSignedUpper k ε A i))
          k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1) x :=
      (Set.indicator_of_mem hxPrefixGood _).symm

/-- Set-integral form of the one-tuple prefix-good contribution. -/
theorem
    annularContractedUpperRetainedPrefixGoodMixedContribution_eq_setIntegral
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedUpperRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedUpperRetainedPrefixGoodMixedContribution
        ε A eta rho N k hr mode hmode p =
      ∫ x in gaussDenominatorPrefixGoodEvent
          (annularContractedUpperRetainedDelayedDepth p)
          (annularDepthAmbientSize N)
          (upperGoodTransferDenominatorTolerance eta rho),
        gaussPrefixMarkedMixedTupleCharacter N
          (fun i ↦ compactValueMarkedRegion
            (activeAnnularOccurrenceSignedLower k ε A i)
            (activeAnnularOccurrenceSignedUpper k ε A i))
          k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedUpperRetainedRealization p).1 x
        ∂uniform01Measure := by
  unfold annularContractedUpperRetainedPrefixGoodMixedContribution
  rw [integral_indicator
    (measurableSet_gaussDenominatorPrefixGoodEvent
      (annularContractedUpperRetainedDelayedDepth p)
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho))]

/-! ## Summed bad-event domination -/

set_option maxHeartbeats 400000 in
/-- For one fixed chronological order, the contracted upper family is a
subfamily of the canonical family, so its simultaneous window indicators
are bounded by the full homogeneous count power. -/
theorem sum_contractedUpperRetained_windowIndicators_for_order_le
    {ε A eta rho : ℝ} {N grid : ℕ}
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (h : Fin (MixedOccurrenceCount k) → ℤ)
    (hh : h ≠ 0)
    (hN : 1 < N) (x : ℝ) :
    (∑ t ∈
        contractedAnnularCanonicalLaterUpperMidpointTupleFamily
          eta rho N k hr e h hh,
      (orderedEventIntersection
        (List.ofFn fun j ↦
          gaussApproximationWindow
            (Real.log (N : ℝ)) (t j) ε A)).indicator
        (fun _x ↦ (1 : ℝ)) x) ≤
      (gaussApproximationWindowCount
        (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
        MixedOccurrenceCount k := by
  classical
  unfold gaussApproximationWindowCount
  exact sum_orderedEventIndicators_le_finiteEventCount_pow
    (Finset.range (annularDepthAmbientSize N))
    (fun n ↦ gaussApproximationWindow
      (Real.log (N : ℝ)) n ε A)
    (contractedAnnularCanonicalLaterUpperMidpointTupleFamily
      eta rho N k hr e h hh)
    (fun t ht j ↦ Finset.mem_range.mpr
      (canonicalAnnularGridTupleFamily_lt_ambient
        hgrid k htime hN e t
        (contractedAnnularCanonicalLaterUpperMidpointTupleFamily_subset_canonical
          k hr e h hh ht) j))
    x

/-- Sum the preceding domination over every chronological order. -/
theorem sum_annularContractedUpperRetained_windowIndicators_le
    {ε A eta rho : ℝ} {N grid : ℕ}
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hN : 1 < N) (x : ℝ) :
    (∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
      ∑ t ∈
          contractedAnnularCanonicalLaterUpperMidpointTupleFamily
            eta rho N k hr e (mode e) (hmode e),
        (orderedEventIntersection
          (List.ofFn fun j ↦
            gaussApproximationWindow
              (Real.log (N : ℝ)) (t j) ε A)).indicator
          (fun _x ↦ (1 : ℝ)) x) ≤
      (Fintype.card
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) : ℝ) *
        (gaussApproximationWindowCount
          (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
          MixedOccurrenceCount k := by
  classical
  have hsum :
      (∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ∑ t ∈
            contractedAnnularCanonicalLaterUpperMidpointTupleFamily
              eta rho N k hr e (mode e) (hmode e),
          (orderedEventIntersection
            (List.ofFn fun j ↦
              gaussApproximationWindow
                (Real.log (N : ℝ)) (t j) ε A)).indicator
            (fun _x ↦ (1 : ℝ)) x) ≤
        ∑ _e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          (gaussApproximationWindowCount
            (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
            MixedOccurrenceCount k := by
    apply Finset.sum_le_sum
    intro e _he
    exact sum_contractedUpperRetained_windowIndicators_for_order_le
      hgrid k hr htime e (mode e) (hmode e) hN x
  calc
    _ ≤ ∑ _e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k,
      (gaussApproximationWindowCount
        (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
        MixedOccurrenceCount k := hsum
    _ = _ := by simp

/-- Reindex the tagged indicator sum as the corresponding nested sum over
orders and raw time tuples. -/
theorem sum_annularContractedUpperRetained_taggedWindowIndicators_eq_nested
    {ε A eta rho : ℝ} {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (x : ℝ) :
    (∑ p : AnnularContractedUpperRetainedTaggedTuple
        eta rho N k hr mode hmode,
      (orderedEventIntersection
        (List.ofFn fun j ↦
          gaussApproximationWindow (Real.log (N : ℝ))
            (annularContractedUpperRetainedTimes p j) ε A)).indicator
        (fun _x ↦ (1 : ℝ)) x) =
      ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ∑ t ∈
          contractedAnnularCanonicalLaterUpperMidpointTupleFamily
            eta rho N k hr e (mode e) (hmode e),
          (orderedEventIntersection
            (List.ofFn fun j ↦
              gaussApproximationWindow
                (Real.log (N : ℝ)) (t j) ε A)).indicator
            (fun _x ↦ (1 : ℝ)) x := by
  classical
  let f := fun
      (e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (p : ↥(contractedAnnularCanonicalLaterUpperMidpointTupleFamily
        eta rho N k hr e (mode e) (hmode e))) ↦
    (orderedEventIntersection
      (List.ofFn fun j ↦
        gaussApproximationWindow (Real.log (N : ℝ))
          (annularContractedUpperRetainedTimes
            (⟨e, p⟩ :
              AnnularContractedUpperRetainedTaggedTuple
                eta rho N k hr mode hmode) j) ε A)).indicator
      (fun _x ↦ (1 : ℝ)) x
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
  simp only [f, annularContractedUpperRetainedTimes]
  exact Finset.sum_attach
    (contractedAnnularCanonicalLaterUpperMidpointTupleFamily
      eta rho N k hr e (mode e) (hmode e))
    (fun t ↦
      (orderedEventIntersection
        (List.ofFn fun j ↦
          gaussApproximationWindow
            (Real.log (N : ℝ)) (t j) ε A)).indicator
        (fun _x ↦ (1 : ℝ)) x)

/-- Finite-`N` comparison localized to the complement of one global
denominator-good event. -/
theorem
    norm_annularContractedUpperRetainedMovingSum_sub_prefixGood_le_badIntegral
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
    ‖annularContractedUpperRetainedMovingSum
          ε A eta rho N k hr mode hmode -
        annularContractedUpperRetainedPrefixGoodMixedSum
          ε A eta rho N k hr mode hmode‖ ≤
      ∫ x in
          (gaussDenominatorLinearGoodEvent 1
            (annularDepthAmbientSize N)
            (upperGoodTransferDenominatorTolerance eta rho))ᶜ,
        2 * ∑ p : AnnularContractedUpperRetainedTaggedTuple
            eta rho N k hr mode hmode,
          (orderedEventIntersection
            (List.ofFn fun j ↦
              gaussApproximationWindow (Real.log (N : ℝ))
                (annularContractedUpperRetainedTimes p j) ε A)).indicator
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
  let f : T → ℝ → ℂ := fun p x ↦
    gaussMovingSignedMarkedTupleIntegrand
      N (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A p.1)
      (flattenedAnnularSignedUpper ε A p.1)
      (mode p.1)
      (annularContractedUpperRetainedTimes p) x
  let g : T → ℝ → ℂ := fun p ↦
    (P p).indicator
      (gaussPrefixMarkedMixedTupleCharacter N B k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedUpperRetainedRealization p).1)
  let E : T → Set ℝ := fun p ↦
    orderedEventIntersection
      (List.ofFn fun j ↦
        gaussApproximationWindow (Real.log (N : ℝ))
          (annularContractedUpperRetainedTimes p j) ε A)
  have hgoodMeas : MeasurableSet good := by
    exact measurableSet_gaussDenominatorLinearGoodEvent
      1 (annularDepthAmbientSize N)
        (upperGoodTransferDenominatorTolerance eta rho)
  have hEMeas : ∀ p ∈ (Finset.univ : Finset T),
      MeasurableSet (E p) := by
    intro p _hp
    dsimp only [E]
    apply measurableSet_orderedEventIntersection
    intro S hS
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hS
    exact measurableSet_gaussApproximationWindow _ _ _ _
  have hfInt : ∀ p ∈ (Finset.univ : Finset T),
      Integrable (f p) uniform01Measure := by
    intro p _hp
    exact integrable_gaussMovingSignedMarkedTupleIntegrand
      N (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A p.1)
      (flattenedAnnularSignedUpper ε A p.1)
      (mode p.1)
      (annularContractedUpperRetainedTimes p)
      uniform01Measure
  have hgInt : ∀ p ∈ (Finset.univ : Finset T),
      Integrable (g p) uniform01Measure := by
    intro p _hp
    dsimp only [g]
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
  have heq :
      ∀ᵐ x ∂uniform01Measure,
        x ∈ good →
          ∀ p ∈ (Finset.univ : Finset T), f p x = g p x := by
    have hall :
        ∀ᵐ x ∂uniform01Measure,
          ∀ p : T, x ∈ good → f p x = g p x := by
      apply Filter.eventually_all.mpr
      intro p
      simpa only [good, f, g, P, B] using!
        ae_annularContractedUpperRetained_moving_eq_prefixGoodMixed_on_globalGood
          hε hεA hgrid hN hW k hr htime hsigned mode hmode
          hsmall hmargin p
    filter_upwards [hall] with x hx hxGood
    intro p _hp
    exact hx p hxGood
  have hbound :
      ∀ᵐ x ∂uniform01Measure,
        ∀ p ∈ (Finset.univ : Finset T),
          ‖f p x‖ ≤ (E p).indicator (fun _x ↦ (1 : ℝ)) x ∧
          ‖g p x‖ ≤ (E p).indicator (fun _x ↦ (1 : ℝ)) x := by
    filter_upwards [ae_nonterminating_uniform01] with x hxUnit
    intro p _hp
    constructor
    · dsimp only [f, E]
      rw [norm_gaussMovingSignedMarkedTupleIntegrand]
      exact
        (Set.indicator_le_indicator_of_subset
          (annularContractedUpperRetained_signedEvent_subset_windowEvent
            hεA hgrid hsigned p)
          (fun _x ↦ by norm_num)) x
    · dsimp only [g]
      rw [norm_indicator_eq_indicator_norm]
      calc
        (P p).indicator
            (fun y ↦ ‖gaussPrefixMarkedMixedTupleCharacter N B k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1 y‖) x ≤
          ‖gaussPrefixMarkedMixedTupleCharacter N B k
            (unflattenedAnnularFourierMode p.1 (mode p.1))
            (annularContractedUpperRetainedRealization p).1 x‖ :=
          indicator_norm_le_norm_self
            (s := P p)
            (f := gaussPrefixMarkedMixedTupleCharacter N B k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedUpperRetainedRealization p).1)
            (a := x)
        _ =
          (mixedTupleEvent
            (fun i ↦ gaussPrefixMarkedEvent N (B i))
            (annularContractedUpperRetainedRealization p).1).indicator
              (fun _x ↦ (1 : ℝ)) x := by
          exact norm_gaussPrefixMarkedMixedTupleCharacter_eq_indicator
            k
            (unflattenedAnnularFourierMode p.1 (mode p.1))
            (annularContractedUpperRetainedRealization p).1 x
        _ ≤ (E p).indicator (fun _x ↦ (1 : ℝ)) x := by
          by_cases hxMixed :
              x ∈ mixedTupleEvent
                (fun i ↦ gaussPrefixMarkedEvent N (B i))
                (annularContractedUpperRetainedRealization p).1
          · have hxWindow :
                x ∈ E p := by
              apply
                annularContractedUpperRetained_mixedEvent_subset_windowEvent_of_mem_Ioc
                  hεA hgrid hsigned p
              · exact ⟨hxUnit.1.1, hxUnit.1.2.le⟩
              · simpa only [B] using! hxMixed
            rw [Set.indicator_of_mem hxMixed,
              Set.indicator_of_mem hxWindow]
          · rw [Set.indicator_of_notMem hxMixed]
            exact Set.indicator_nonneg (fun _x ↦ by norm_num) x
  have hcompare :=
    norm_sum_integral_sub_le_goodCompl_indicatorSum
      uniform01Measure (Finset.univ : Finset T)
      good hgoodMeas E hEMeas f g hfInt hgInt heq hbound
  unfold annularContractedUpperRetainedMovingSum
    annularContractedUpperRetainedMovingContribution
    annularContractedUpperRetainedPrefixGoodMixedSum
    annularContractedUpperRetainedPrefixGoodMixedContribution
  rw [← Finset.sum_sub_distrib]
  simpa only [T, good, E, f, g, P, B] using! hcompare

/-- The preceding finite-family integral is bounded by a fixed power of
the homogeneous approximation-window count on the global bad event. -/
theorem
    norm_annularContractedUpperRetainedMovingSum_sub_prefixGood_le_badMoment
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
    ‖annularContractedUpperRetainedMovingSum
          ε A eta rho N k hr mode hmode -
        annularContractedUpperRetainedPrefixGoodMixedSum
          ε A eta rho N k hr mode hmode‖ ≤
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
  let bad : Set ℝ :=
    gaussDenominatorLinearBadEvent 1
      (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)
  have hfirst :=
    norm_annularContractedUpperRetainedMovingSum_sub_prefixGood_le_badIntegral
      hε hεA hgrid hN hW k hr htime hsigned mode hmode
      hsmall hmargin
  rw [← gaussDenominatorLinearBadEvent_eq_compl
    1 (annularDepthAmbientSize N)
      (upperGoodTransferDenominatorTolerance eta rho)] at hfirst
  refine hfirst.trans ?_
  have hleftInt :
      Integrable
        (fun x ↦
          2 * ∑ p : AnnularContractedUpperRetainedTaggedTuple
              eta rho N k hr mode hmode,
            (orderedEventIntersection
              (List.ofFn fun j ↦
                gaussApproximationWindow (Real.log (N : ℝ))
                  (annularContractedUpperRetainedTimes p j) ε A)).indicator
              (fun _x ↦ (1 : ℝ)) x)
        (uniform01Measure.restrict bad) := by
    apply Integrable.mono_measure _ Measure.restrict_le_self
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro p _hp
    apply (integrable_const (1 : ℝ)).indicator
    apply measurableSet_orderedEventIntersection
    intro S hS
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hS
    exact measurableSet_gaussApproximationWindow _ _ _ _
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
  dsimp only
  rw [
    sum_annularContractedUpperRetained_taggedWindowIndicators_eq_nested
      k hr mode hmode x]
  have hpoint :=
    sum_annularContractedUpperRetained_windowIndicators_le
      (ε := ε) (A := A) (eta := eta) (rho := rho) (N := N)
      hgrid k hr htime mode hmode (by omega) x
  simpa only [mul_assoc] using!
    mul_le_mul_of_nonneg_left hpoint (by norm_num : (0 : ℝ) ≤ 2)

/-- For fixed positive contraction parameters, the transfer tolerance
eventually leaves the deterministic time-box contraction margin required
by the exact continued-fraction bridge. -/
theorem
    eventually_upperGoodTransferDenominatorTolerance_mul_ambient_le_margin
    {eta rho : ℝ} (heta : 0 < eta) (hrho : 0 < rho) :
    ∀ᶠ N : ℕ in atTop,
      upperGoodTransferDenominatorTolerance eta rho *
          (annularDepthAmbientSize N : ℝ) ≤
        eta * Real.log (N : ℝ) := by
  let Delta := upperGoodTransferDenominatorTolerance eta rho
  have hminPos : 0 < min eta rho := lt_min heta hrho
  have hminLe : min eta rho ≤ eta := min_le_left _ _
  have hlimit :
      Delta * (1 / gaussRoofMean) < eta := by
    dsimp only [Delta, upperGoodTransferDenominatorTolerance]
    field_simp [ne_of_gt gaussRoofMean_pos]
    nlinarith
  have hratio :
      Tendsto
        (fun N : ℕ ↦
          Delta *
            ((annularDepthAmbientSize N : ℝ) /
              Real.log (N : ℝ)))
        atTop (nhds (Delta * (1 / gaussRoofMean))) :=
    tendsto_const_nhds.mul tendsto_annularDepthAmbientSize_div_log
  have hlt := hratio.eventually_lt_const hlimit
  filter_upwards
    [hlt,
      tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
      N hltN hlog
  have hdiv :
      Delta * (annularDepthAmbientSize N : ℝ) /
          Real.log (N : ℝ) < eta := by
    calc
      Delta * (annularDepthAmbientSize N : ℝ) /
          Real.log (N : ℝ) =
          Delta *
            ((annularDepthAmbientSize N : ℝ) /
              Real.log (N : ℝ)) := by ring
      _ < eta := hltN
  exact ((div_lt_iff₀ hlog).mp hdiv).le

/-- The exact contracted moving aggregate and the delayed-prefix-good full
mixed-character aggregate have the same limit. -/
theorem
    tendsto_annularContractedUpperRetainedMovingSum_sub_prefixGood_zero
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
        annularContractedUpperRetainedMovingSum
            ε A eta rho N k hr mode hmode -
          annularContractedUpperRetainedPrefixGoodMixedSum
            ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
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
  have hmajor :
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
        ‖annularContractedUpperRetainedMovingSum
              ε A eta rho N k hr mode hmode -
            annularContractedUpperRetainedPrefixGoodMixedSum
              ε A eta rho N k hr mode hmode‖ ≤
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
    simpa only [C, mul_assoc] using!
      norm_annularContractedUpperRetainedMovingSum_sub_prefixGood_le_badMoment
        hε hεA hgrid hN hWN k hr htime hsigned mode hmode
        hsmallN hmarginN
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _N ↦ norm_nonneg _) hupper hmajor

end

end Erdos1002
