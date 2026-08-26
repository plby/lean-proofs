import ErdosProblems.Erdos1002.GaussPrefixAnnularLiteralTransfer
import ErdosProblems.Erdos1002.GaussPrefixAnnularMidpointSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Contracted upper-retained annular tuples

The mixed-prefix character is used only after contracting the deterministic
time boxes away from their endpoints.  This file performs that contraction
for the upper-retained midpoint family and proves that restoring the removed
tuples costs no more than the already-established global annular
time-boundary mass.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularUpperContractedPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- Upper-retained tuples whose every coordinate also belongs to its
contracted canonical time box. -/
def contractedAnnularCanonicalLaterUpperMidpointTupleFamily
    (eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  annularCanonicalLaterUpperMidpointTupleFamily
      rho N k hr e mode hmode ∩
    contractedCanonicalAnnularGridTupleFamily N eta k e

@[simp] theorem
    mem_contractedAnnularCanonicalLaterUpperMidpointTupleFamily_iff
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k}
    {mode : Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : mode ≠ 0}
    {t : Fin (MixedOccurrenceCount k) → ℕ} :
    t ∈ contractedAnnularCanonicalLaterUpperMidpointTupleFamily
        eta rho N k hr e mode hmode ↔
      t ∈ annularCanonicalLaterUpperMidpointTupleFamily
          rho N k hr e mode hmode ∧
        t ∈ contractedCanonicalAnnularGridTupleFamily N eta k e := by
  simp [contractedAnnularCanonicalLaterUpperMidpointTupleFamily]

/-- Contracted membership supplies the literal contracted depth-box
condition at every chronological coordinate. -/
theorem contractedAnnularCanonicalLaterUpperMidpointTupleFamily_boxes
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k}
    {mode : Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : mode ≠ 0}
    {t : Fin (MixedOccurrenceCount k) → ℕ}
    (ht : t ∈ contractedAnnularCanonicalLaterUpperMidpointTupleFamily
      eta rho N k hr e mode hmode) :
    ∀ j, t j ∈ contractedAnnularTimeDepthBox N eta (e j).1 := by
  have htContracted :=
    (mem_contractedAnnularCanonicalLaterUpperMidpointTupleFamily_iff.mp
      ht).2
  obtain ⟨F, _horder, hboxes, htimes⟩ :=
    mem_canonicalMixedOrderParityBoxTimes_iff.mp htContracted
  intro j
  rw [← htimes]
  exact (hboxes j).1

theorem
    contractedAnnularCanonicalLaterUpperMidpointTupleFamily_subset_upper
    {eta rho : ℝ} {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    contractedAnnularCanonicalLaterUpperMidpointTupleFamily
        eta rho N k hr e mode hmode ⊆
      annularCanonicalLaterUpperMidpointTupleFamily
        rho N k hr e mode hmode := by
  intro t ht
  exact
    (mem_contractedAnnularCanonicalLaterUpperMidpointTupleFamily_iff.mp
      ht).1

theorem
    contractedAnnularCanonicalLaterUpperMidpointTupleFamily_subset_canonical
    {eta rho : ℝ} {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    contractedAnnularCanonicalLaterUpperMidpointTupleFamily
        eta rho N k hr e mode hmode ⊆
      canonicalAnnularGridTupleFamily N k e := by
  intro t ht
  have hupper :=
    contractedAnnularCanonicalLaterUpperMidpointTupleFamily_subset_upper
      k hr e mode hmode ht
  have hinterior :=
    (mem_laterUpperMidpointNatTupleFamily_iff.mp hupper).1
  have hlate := (mem_lateFirstNatTupleFamily_iff.mp hinterior).1
  exact (mem_separatedNatTupleFamily_iff.mp hlate).1

theorem
    contractedAnnularCanonicalLaterUpperMidpointTupleFamily_chronological
    {eta rho : ℝ} {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ contractedAnnularCanonicalLaterUpperMidpointTupleFamily
      eta rho N k hr e mode hmode) :
    IsChronologicalNatTuple t :=
  canonicalAnnularGridTupleFamily_chronological N k e t
    (contractedAnnularCanonicalLaterUpperMidpointTupleFamily_subset_canonical
      k hr e mode hmode ht)

/-- The upper tuples deleted by contraction form a subfamily of the global
expanded-minus-contracted annular time boundary. -/
theorem upperRetained_sdiff_contracted_subset_timeBoundary
    {rho : ℝ} {N grid : ℕ} {eta : ℝ} (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    annularCanonicalLaterUpperMidpointTupleFamily
          rho N k hr e mode hmode \
        contractedAnnularCanonicalLaterUpperMidpointTupleFamily
          eta rho N k hr e mode hmode ⊆
      annularCanonicalTimeBoundaryTupleFamily N eta k e := by
  intro t ht
  rw [Finset.mem_sdiff] at ht
  have hcanonical :
      t ∈ canonicalAnnularGridTupleFamily N k e := by
    have hinterior :=
      (mem_laterUpperMidpointNatTupleFamily_iff.mp ht.1).1
    have hlate := (mem_lateFirstNatTupleFamily_iff.mp hinterior).1
    exact (mem_separatedNatTupleFamily_iff.mp hlate).1
  have hnotContracted :
      t ∉ contractedCanonicalAnnularGridTupleFamily N eta k e := by
    intro hc
    exact ht.2
      (mem_contractedAnnularCanonicalLaterUpperMidpointTupleFamily_iff.mpr
        ⟨ht.1, hc⟩)
  exact mem_annularCanonicalTimeBoundaryTupleFamily_iff.mpr
    ⟨canonicalAnnularGridTupleFamily_subset_expanded
      heta k e hcanonical, hnotContracted⟩

/-- For one chronological tag, restoring the contracted upper family costs
at most the positive global time-boundary mass for that tag. -/
theorem norm_upperRetained_sub_contracted_le_timeBoundary_mass
    {ε A rho : ℝ} {grid N : ℕ} {eta : ℝ} (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    ‖uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          mode
          (annularCanonicalLaterUpperMidpointTupleFamily
            rho N k hr e mode hmode) -
        uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          mode
          (contractedAnnularCanonicalLaterUpperMidpointTupleFamily
            eta rho N k hr e mode hmode)‖ ≤
      movingSignedApproximationTupleMassSum
        uniform01Measure (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (annularCanonicalTimeBoundaryTupleFamily N eta k e) := by
  calc
    _ ≤ movingSignedApproximationTupleMassSum
          uniform01Measure (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          (annularCanonicalLaterUpperMidpointTupleFamily
              rho N k hr e mode hmode \
            contractedAnnularCanonicalLaterUpperMidpointTupleFamily
              eta rho N k hr e mode hmode) :=
      norm_movingSignedMarkedFourierTupleSum_sub_le_sdiff_mass
        uniform01Measure N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) mode
        (contractedAnnularCanonicalLaterUpperMidpointTupleFamily
          eta rho N k hr e mode hmode)
        (annularCanonicalLaterUpperMidpointTupleFamily
          rho N k hr e mode hmode)
        (contractedAnnularCanonicalLaterUpperMidpointTupleFamily_subset_upper
          k hr e mode hmode)
    _ ≤ movingSignedApproximationTupleMassSum
          uniform01Measure (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          (annularCanonicalTimeBoundaryTupleFamily N eta k e) := by
      unfold movingSignedApproximationTupleMassSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact upperRetained_sdiff_contracted_subset_timeBoundary
          heta k hr e mode hmode
      · intro _t _ht _hnot
        positivity

/-- Absolute restoration error over all tags is bounded by the already
audited global time-boundary mass. -/
theorem sum_norm_upperRetained_sub_contracted_le_timeBoundary_mass
    {ε A rho : ℝ} {grid N : ℕ} {eta : ℝ} (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    (∑ e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k,
      ‖uniformMovingSignedMarkedFourierTupleSum
            N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (mode e)
            (annularCanonicalLaterUpperMidpointTupleFamily
              rho N k hr e (mode e) (hmode e)) -
          uniformMovingSignedMarkedFourierTupleSum
            N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (mode e)
            (contractedAnnularCanonicalLaterUpperMidpointTupleFamily
              eta rho N k hr e (mode e) (hmode e))‖) ≤
      aggregateUniformMovingSignedApproximationTupleMassSum
        (β := Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k)
        (Real.log (N : ℝ))
        (fun e ↦ flattenedAnnularSignedLower ε A e)
        (fun e ↦ flattenedAnnularSignedUpper ε A e)
        (fun e ↦ annularCanonicalTimeBoundaryTupleFamily N eta k e) := by
  unfold aggregateUniformMovingSignedApproximationTupleMassSum
    aggregateMovingSignedApproximationTupleMassSum
  exact Finset.sum_le_sum fun e _he ↦
    norm_upperRetained_sub_contracted_le_timeBoundary_mass
      heta k hr e (mode e) (hmode e)

/-- Iterated restoration of the upper time-box contraction.  The norm is
inside the tag sum, and the order of limits is explicit:
`N → ∞` for fixed `eta = 1/(m+1)`, then `m → ∞`. -/
theorem eventually_eventually_sum_norm_upperRetained_sub_contracted_lt
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (rho : ℝ) {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      (∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ‖uniformMovingSignedMarkedFourierTupleSum
              N (Real.log (N : ℝ))
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e)
              (mode e)
              (annularCanonicalLaterUpperMidpointTupleFamily
                rho N k hr e (mode e) (hmode e)) -
            uniformMovingSignedMarkedFourierTupleSum
              N (Real.log (N : ℝ))
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e)
              (mode e)
              (contractedAnnularCanonicalLaterUpperMidpointTupleFamily
                (1 / ((m : ℝ) + 1)) rho N k hr e
                (mode e) (hmode e))‖) < delta := by
  have hboundary :=
    eventually_eventually_aggregateUniform_annularTimeBoundary_mass_lt
      hε hεA hgrid k hr htime hsigned hdelta
  filter_upwards [hboundary] with m hm
  filter_upwards [hm] with N hN
  exact lt_of_le_of_lt
    (sum_norm_upperRetained_sub_contracted_le_timeBoundary_mass
      (eta := 1 / ((m : ℝ) + 1)) (by positivity)
      k hr mode hmode)
    hN

end

end Erdos1002
