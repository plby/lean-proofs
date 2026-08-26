import ErdosProblems.Erdos1002.GaussPrefixAnnularLiteralTransfer
import ErdosProblems.Erdos1002.GaussPrefixAnnularLowerRetained
import ErdosProblems.Erdos1002.GaussPrefixAnnularMidpointAssembly
import ErdosProblems.Erdos1002.IteratedBoundaryRestoration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Restoring the lower retained time boxes

The lower oscillatory estimate uses a fixed contraction of every annular
time box.  This file proves that the removed lower-retained tuples lie in
the global annular time-boundary family and then performs the iterated
`N → ∞`, `eta ↓ 0` restoration.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularLowerRestorationPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- The lower-retained tuples removed by a time-box contraction are
contained in the global expanded-minus-contracted boundary family. -/
theorem lowerRetained_sdiff_contracted_subset_timeBoundary
    {eta rho : ℝ} (heta : 0 ≤ eta)
    {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    annularCanonicalLaterLowerMidpointTupleFamily
          rho N k hr e mode hmode \
        contractedAnnularCanonicalLaterLowerMidpointTupleFamily
          eta rho N k hr e mode hmode ⊆
      annularCanonicalTimeBoundaryTupleFamily N eta k e := by
  intro t ht
  have hlower := (Finset.mem_sdiff.mp ht).1
  have hnotContracted := (Finset.mem_sdiff.mp ht).2
  have hinterior :=
    (mem_laterLowerMidpointNatTupleFamily_iff.mp hlower).1
  have hlate := (mem_lateFirstNatTupleFamily_iff.mp hinterior).1
  have hcanonical :=
    (mem_separatedNatTupleFamily_iff.mp hlate).1
  apply mem_annularCanonicalTimeBoundaryTupleFamily_iff.mpr
  constructor
  · exact canonicalAnnularGridTupleFamily_subset_expanded
      heta k e hcanonical
  · intro hcontracted
    apply hnotContracted
    apply
      mem_contractedAnnularCanonicalLaterLowerMidpointTupleFamily_iff.mpr
    refine ⟨hlower, ?_⟩
    simpa only [lowerRetainedContractedCanonicalAnnularGridTupleFamily,
      contractedCanonicalAnnularGridTupleFamily] using! hcontracted

/-- One lower-retained Fourier coefficient changes by no more than the
positive mass of the global time-boundary family. -/
theorem norm_lowerRetained_sub_contracted_le_timeBoundary_mass
    {ε A eta rho : ℝ} (heta : 0 ≤ eta)
    {N grid : ℕ}
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
          (annularCanonicalLaterLowerMidpointTupleFamily
            rho N k hr e mode hmode) -
        uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          mode
          (contractedAnnularCanonicalLaterLowerMidpointTupleFamily
            eta rho N k hr e mode hmode)‖ ≤
      movingSignedApproximationTupleMassSum
        uniform01Measure (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (annularCanonicalTimeBoundaryTupleFamily N eta k e) := by
  have hsubset :
      contractedAnnularCanonicalLaterLowerMidpointTupleFamily
          eta rho N k hr e mode hmode ⊆
        annularCanonicalLaterLowerMidpointTupleFamily
          rho N k hr e mode hmode := by
    intro t ht
    exact
      (mem_contractedAnnularCanonicalLaterLowerMidpointTupleFamily_iff.mp
        ht).1
  calc
    _ ≤ movingSignedApproximationTupleMassSum
          uniform01Measure (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          (annularCanonicalLaterLowerMidpointTupleFamily
              rho N k hr e mode hmode \
            contractedAnnularCanonicalLaterLowerMidpointTupleFamily
              eta rho N k hr e mode hmode) :=
      norm_movingSignedMarkedFourierTupleSum_sub_le_sdiff_mass
        uniform01Measure N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        mode
        (contractedAnnularCanonicalLaterLowerMidpointTupleFamily
          eta rho N k hr e mode hmode)
        (annularCanonicalLaterLowerMidpointTupleFamily
          rho N k hr e mode hmode)
        hsubset
    _ ≤ movingSignedApproximationTupleMassSum
          uniform01Measure (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          (annularCanonicalTimeBoundaryTupleFamily N eta k e) := by
      unfold movingSignedApproximationTupleMassSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact lowerRetained_sdiff_contracted_subset_timeBoundary
          heta k hr e mode hmode
      · intro _t _ht _hnot
        positivity

/-- Summed version of the lower contraction error, with the norm retained
inside the chronological-tag sum. -/
theorem sum_norm_lowerRetained_sub_contracted_le_timeBoundary_mass
    {ε A eta rho : ℝ} (heta : 0 ≤ eta)
    {N grid : ℕ}
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
            (annularCanonicalLaterLowerMidpointTupleFamily
              rho N k hr e (mode e) (hmode e)) -
        uniformMovingSignedMarkedFourierTupleSum
            N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (mode e)
            (contractedAnnularCanonicalLaterLowerMidpointTupleFamily
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
    norm_lowerRetained_sub_contracted_le_timeBoundary_mass
      heta k hr e (mode e) (hmode e)

/-- The lower contraction error is uniformly small in the correct
iterated order `eta = 1/(m+1) ↓ 0`, then `N → ∞`. -/
theorem eventually_eventually_sum_norm_lowerRetained_sub_contracted_lt
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
              (annularCanonicalLaterLowerMidpointTupleFamily
                rho N k hr e (mode e) (hmode e)) -
            uniformMovingSignedMarkedFourierTupleSum
              N (Real.log (N : ℝ))
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e)
              (mode e)
              (contractedAnnularCanonicalLaterLowerMidpointTupleFamily
                (1 / ((m : ℝ) + 1)) rho N k hr e
                (mode e) (hmode e))‖) < delta := by
  have hboundary :=
    eventually_eventually_aggregateUniform_annularTimeBoundary_mass_lt
      hε hεA hgrid k hr htime hsigned hdelta
  filter_upwards [hboundary] with m hm
  filter_upwards [hm] with N hN
  exact lt_of_le_of_lt
    (sum_norm_lowerRetained_sub_contracted_le_timeBoundary_mass
      (eta := 1 / ((m : ℝ) + 1)) (by positivity)
      k hr mode hmode)
    hN

/-- Fixed-contraction version of lower retained Fourier cancellation. -/
def GaussPrefixAnnularContractedLowerRetainedFourierLimits : Prop :=
  ∀ {ε A : ℝ}, 0 < ε → ε < A →
    ∀ {grid : ℕ}, 0 < grid →
      ∀ (k : AnnularGridIndex grid → ℕ),
        ∀ (hr : 0 < MixedOccurrenceCount k),
        ∀ (_htime : ∀ i, 0 < k i → i.time.1 < grid),
        ∀ (_hsigned : ∀ i, 0 < k i → i.signed.1 < grid),
        ∀ (mode :
          (Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k) →
            Fin (MixedOccurrenceCount k) → ℤ),
          ∀ (hmode : ∀ e, mode e ≠ 0),
          ∀ rho : ℝ, 0 < rho →
            ∀ eta : ℝ, 0 < eta →
              Tendsto
                (fun N : ℕ ↦
                  ∑ e : Fin (MixedOccurrenceCount k) ≃
                      GaussPrefixMixedOccurrence k,
                    uniformMovingSignedMarkedFourierTupleSum
                      N (Real.log (N : ℝ))
                      (flattenedAnnularSignedLower ε A e)
                      (flattenedAnnularSignedUpper ε A e)
                      (mode e)
                      (contractedAnnularCanonicalLaterLowerMidpointTupleFamily
                        eta rho N k hr e (mode e) (hmode e)))
                atTop (nhds 0)

/-- Fixed-contraction lower cancellation restores to the exact lower
retained interface. -/
theorem gaussPrefixAnnularLowerRetainedFourierLimits_of_contracted
    (hcontracted :
      GaussPrefixAnnularContractedLowerRetainedFourierLimits) :
    GaussPrefixAnnularLowerRetainedFourierLimits := by
  intro ε A hε hεA grid hgrid k hr htime hsigned mode hmode rho hrho
  let full : ℕ → ℂ := fun N ↦
    annularCanonicalUniformLowerRetainedMarkedFourierSum
      ε A rho N k hr mode hmode
  let contracted : ℕ → ℕ → ℂ := fun m N ↦
    ∑ e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k,
      uniformMovingSignedMarkedFourierTupleSum
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (mode e)
        (contractedAnnularCanonicalLaterLowerMidpointTupleFamily
          (1 / ((m : ℝ) + 1)) rho N k hr e
          (mode e) (hmode e))
  let boundary : ℕ → ℕ → ℝ := fun m N ↦
    ∑ e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k,
      ‖uniformMovingSignedMarkedFourierTupleSum
            N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (mode e)
            (annularCanonicalLaterLowerMidpointTupleFamily
              rho N k hr e (mode e) (hmode e)) -
        uniformMovingSignedMarkedFourierTupleSum
            N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (mode e)
            (contractedAnnularCanonicalLaterLowerMidpointTupleFamily
              (1 / ((m : ℝ) + 1)) rho N k hr e
              (mode e) (hmode e))‖
  have hdifference :
      ∀ m : ℕ, ∀ᶠ N : ℕ in atTop,
        ‖full N - contracted m N‖ ≤ boundary m N := by
    intro m
    exact Eventually.of_forall fun N ↦ by
      dsimp only [full, contracted, boundary,
        annularCanonicalUniformLowerRetainedMarkedFourierSum]
      rw [← Finset.sum_sub_distrib]
      exact norm_sum_le _ _
  have hfixed :
      ∀ m : ℕ, Tendsto (contracted m) atTop (nhds 0) := by
    intro m
    have heta : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    simpa only [contracted] using!
      hcontracted hε hεA hgrid k hr htime hsigned
        mode hmode rho hrho (1 / ((m : ℝ) + 1)) heta
  have hboundary :
      ∀ {δ : ℝ}, 0 < δ →
        ∀ᶠ m : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
          boundary m N < δ := by
    intro δ hδ
    simpa only [boundary] using!
      eventually_eventually_sum_norm_lowerRetained_sub_contracted_lt
        hε hεA rho hgrid k hr htime hsigned mode hmode hδ
  simpa only [full] using!
    tendsto_zero_of_iterated_contracted_boundary
      full contracted boundary hdifference hfixed hboundary

end

end Erdos1002
